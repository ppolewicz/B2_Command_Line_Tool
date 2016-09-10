######################################################################
#
# File: utils.py
#
# Copyright 2016 Backblaze Inc. All Rights Reserved.
#
# License https://www.backblaze.com/using_b2_code.html
#
######################################################################

from __future__ import division, print_function

from collections import OrderedDict
from functools import wraps
import hashlib
import inspect
import itertools
import logging
import re
import shutil
import tempfile
import time

import six
from six.moves import urllib

try:
    import concurrent.futures as futures
except ImportError:
    import futures

# Global variable that says whether the app is shutting down
_shutting_down = False

EMPTY_TUPLE = tuple()


def set_shutting_down():
    global _shutting_down
    _shutting_down = True


def raise_if_shutting_down():
    if _shutting_down:
        raise KeyboardInterrupt()


def current_time_millis():
    """
    File times are in integer milliseconds, to avoid roundoff errors.
    """
    return int(round(time.time() * 1000))


def interruptible_get_result(future):
    """
    Waits for the result of a future in a way that can be interrupted
    by a KeyboardInterrupt.

    This is not necessary in Python 3, but is needed for Python 2.
    """
    while True:
        try:
            return future.result(timeout=1.0)
        except futures.TimeoutError:
            pass


def b2_url_encode(s):
    """URL-encodes a unicode string to be sent to B2 in an HTTP header.
    """
    return urllib.parse.quote(s.encode('utf-8'))


def b2_url_decode(s):
    """Decodes a Unicode string returned from B2 in an HTTP header.

    Returns a Python unicode string.
    """
    # Use str() to make sure that the input to unquote is a str, not
    # unicode, which ensures that the result is a str, which allows
    # the decoding to work properly.
    return urllib.parse.unquote_plus(str(s)).decode('utf-8')


def choose_part_ranges(content_length, minimum_part_size):
    """
    Returns a list of (offset, length) for the parts of a large file.
    """

    # If the file is at least twice the minimum part size, we are guaranteed
    # to be able to break it into multiple parts that are all at least
    # the minimum part size.
    assert minimum_part_size * 2 <= content_length

    # How many parts can we make?
    part_count = min(content_length // minimum_part_size, 10000)
    assert 2 <= part_count

    # All of the parts, except the last, are the same size.  The
    # last one may be bigger.
    part_size = content_length // part_count
    last_part_size = content_length - (part_size * (part_count - 1))
    assert minimum_part_size <= last_part_size

    # Make all of the parts except the last
    parts = [(i * part_size, part_size) for i in six.moves.range(part_count - 1)]

    # Add the last part
    start_of_last = (part_count - 1) * part_size
    last_part = (start_of_last, content_length - start_of_last)
    parts.append(last_part)

    return parts


def hex_sha1_of_stream(input_stream, content_length):
    """
    Returns the 40-character hex SHA1 checksum of the first content_length
    bytes in the input stream.
    """
    remaining = content_length
    block_size = 1024 * 1024
    digest = hashlib.sha1()
    while remaining != 0:
        to_read = min(remaining, block_size)
        data = input_stream.read(to_read)
        if len(data) != to_read:
            raise ValueError(
                'content_length(%s) is more than the size of the file' % content_length
            )
        digest.update(data)
        remaining -= to_read
    return digest.hexdigest()


def hex_sha1_of_bytes(data):
    """
    Returns the 40-character hex SHA1 checksum of the first content_length
    bytes in the input stream.
    """
    return hashlib.sha1(data).hexdigest()


def validate_b2_file_name(name):
    """
    Raises a ValueError if the name is not a valid B2 file name.

    :param name: a string
    :return: None
    """
    if not isinstance(name, six.string_types):
        raise ValueError('file name must be a string, not bytes')
    name_utf8 = name.encode('utf-8')
    if len(name_utf8) < 1:
        raise ValueError('file name too short (0 utf-8 bytes)')
    if 1000 < len(name_utf8):
        raise ValueError('file name too long (more than 1000 utf-8 bytes)')
    if name[0] == '/':
        raise ValueError("file names must not start with '/'")
    if name[-1] == '/':
        raise ValueError("file names must not end with '/'")
    if '\\' in name:
        raise ValueError("file names must not contain '\\'")
    if '//' in name:
        raise ValueError("file names must not contain '//'")
    if chr(127) in name:
        raise ValueError("file names must not contain DEL")
    if any(250 < len(segment) for segment in name_utf8.split(six.b('/'))):
        raise ValueError("file names segments (between '/') can be at most 250 utf-8 bytes")


class BytesIoContextManager(object):
    """
    A simple wrapper for a BytesIO that makes it look like
    a file-like object that can be a context manager.
    """

    def __init__(self, byte_data):
        self.byte_data = byte_data

    def __enter__(self):
        return six.BytesIO(self.byte_data)

    def __exit__(self, type_, value, traceback):
        return None  # don't hide exception


class TempDir(object):
    """
    Context manager that creates and destroys a temporary directory.
    """

    def __enter__(self):
        """
        Returns the unicode path to the temp dir.
        """
        self.dirpath = six.u(tempfile.mkdtemp())
        return self.dirpath

    def __exit__(self, exc_type, exc_val, exc_tb):
        shutil.rmtree(self.dirpath)
        return None  # do not hide exception


def _pick_scale_and_suffix(x):
    # suffixes for different scales
    suffixes = ' kMGTP'

    # We want to use the biggest suffix that makes sense.
    ref_digits = str(int(x))
    index = (len(ref_digits) - 1) // 3
    suffix = suffixes[index]
    if suffix == ' ':
        suffix = ''

    scale = 1000**index
    return (scale, suffix)


def format_and_scale_number(x, unit):
    """
    Picks a good scale for representing a number and formats it.
    """

    # simple case for small numbers
    if x < 1000:
        return '%d %s' % (x, unit)

    # pick a scale
    (scale, suffix) = _pick_scale_and_suffix(x)

    # decide how many digits after the decimal to display
    scaled = x / scale
    if scaled < 10.0:
        fmt = '%1.2f %s%s'
    elif scaled < 100.0:
        fmt = '%1.1f %s%s'
    else:
        fmt = '%1.0f %s%s'

    # format it
    return fmt % (scaled, suffix, unit)


def format_and_scale_fraction(numerator, denominator, unit):
    """
    Picks a good scale for representing a fraction, and formats it.
    """

    # simple case for small numbers
    if denominator < 1000:
        return '%d / %d %s' % (numerator, denominator, unit)

    # pick a scale
    (scale, suffix) = _pick_scale_and_suffix(denominator)

    # decide how many digits after the decimal to display
    scaled_denominator = denominator / scale
    if scaled_denominator < 10.0:
        fmt = '%1.2f / %1.2f %s%s'
    elif scaled_denominator < 100.0:
        fmt = '%1.1f / %1.1f %s%s'
    else:
        fmt = '%1.0f / %1.0f %s%s'

    # format it
    scaled_numerator = numerator / scale
    return fmt % (scaled_numerator, scaled_denominator, suffix, unit)


_CAMELCASE_TO_UNDERSCORE_RE = re.compile('((?<=[a-z0-9])[A-Z]|(?!^)[A-Z](?=[a-z]))')


def camelcase_to_underscore(input_):
    return _CAMELCASE_TO_UNDERSCORE_RE.sub(r'_\1', input_).lower()


def repr_dict_deterministically(dict_):
    # a simple version had a disadvantage of outputting dictionary keys in random order.
    # It was hard to read. Therefore we sort items by key.
    fields = ', '.join('%s: %s' % (repr(k), repr(v)) for k, v in sorted(six.iteritems(dict_)))
    return '{%s}' % (fields,)


def get_class_that_defined_method(meth):
    if inspect.ismethod(meth):
        for cls in inspect.getmro(meth.__self__.__class__):
            if cls.__dict__.get(meth.__name__) is meth:
                return cls
        meth = meth.__func__  # fallback to __qualname__ parsing
    if inspect.isfunction(meth):
        if not hasattr(meth, '__qualname__'):
            pass  # python too old
        else:
            cls = getattr(
                inspect.getmodule(meth),
                meth.__qualname__.split('.<locals>', 1)[0].rsplit('.', 1)[0]
            )
            if isinstance(cls, type):
                return cls
    return None


class trace_call(object):
    """
    A decorator which causes the function execution to be logged using a passed logger
    """

    LEVEL = logging.DEBUG

    def __init__(self, logger, only=None, skip=None):
        """
            only - if not None, contains a whitelist (tuple of names) of arguments
                   that are safe to be logged. All others can not be logged.
            skip - if not None, contains a whitelist (tuple of names) of arguments
                   that are not safe to be logged.
        """
        self.logger = logger
        self.only = only
        self.skip = skip

    def __call__(self, function):
        @wraps(function)
        def wrapper(*args, **kwargs):
            if self.logger.isEnabledFor(self.LEVEL):
                args_names = OrderedDict.fromkeys(
                    itertools.chain(inspect.getargspec(function)[0], six.iterkeys(kwargs))
                )
                args_dict = OrderedDict(
                    itertools.chain(six.moves.zip(args_names, args), six.iteritems(kwargs))
                )

                # filter arguments
                output_arg_names = []
                skipped_arg_names = []
                if self.skip is not None and self.only is not None:
                    for arg in six.iterkeys(args_dict):
                        if arg in self.only and arg not in self.skip:
                            output_arg_names.append(arg)
                        else:
                            skipped_arg_names.append(arg)
                elif self.only is not None:
                    for arg in six.iterkeys(args_dict):
                        if arg in self.only:
                            output_arg_names.append(arg)
                        else:
                            skipped_arg_names.append(arg)
                elif self.skip is not None:
                    for arg in six.iterkeys(args_dict):
                        if arg in self.skip:
                            skipped_arg_names.append(arg)
                        else:
                            output_arg_names.append(arg)
                else:
                    output_arg_names = args_dict

                # format output
                suffix = ''
                if skipped_arg_names:
                    suffix = ' (hidden args: %s)' % (', '.join(skipped_arg_names))
                arguments = ', '.join('%s=%s' % (k, repr(args_dict[k])) for k in output_arg_names)

                function_name = function.__name__
                klass = get_class_that_defined_method(function)
                if klass is not None:
                    function_name = '%s.%s' % (klass.__name__, function_name)

                # actually log the call
                self.logger.log(self.LEVEL, 'calling %s(%s)%s', function_name, arguments, suffix)
            return function(*args, **kwargs)

        return wrapper


class limit_trace_arguments(object):
    """
    A decorator which causes the function execution logging to omit some fields
    """

    def __init__(self, only=None, skip=None):
        """
            only - if not None, contains a whitelist (tuple of names) of arguments
                   that are safe to be logged. All others can not be logged.
            skip - if not None, contains a whitelist (tuple of names) of arguments
                   that are not safe to be logged.
        """
        self.only = only
        self.skip = skip

    def __call__(self, function):
        function._trace_only = self.only
        function._trace_skip = self.skip
        return function


def disable_trace(function):
    """
    A decorator which suppresses the function execution logging
    """
    function._trace_disable = True
    return function


class TracePublicCallsMeta(type):
    """
    A metaclass which logs calls to public methods of *inheriting* classes.
    Perhaps a class decorator could do the same thing, but class decorators
    are not inherited and this way we are sure that all ancestors will do the
    right thing.
    """

    def __new__(mcs, name, bases, attrs, **kwargs):

        # *magic*: an educated guess is made on how the module that the
        # processed class is created in would get its logger.
        # It is assumed that the popular convention recommended by the
        # developers of standard library (`logger = logging.getLogger(__name__)`)
        # is used.
        target_logger = logging.getLogger(attrs['__module__'])

        for attribute_name in attrs:
            attribute_value = attrs[attribute_name]

            if not callable(attribute_value):
                continue  # it is a field
            if attribute_name.startswith('_'):
                continue  # it is a _protected or a __private method or __this_kind__
            if hasattr(attribute_value, '_trace_disable'):
                continue

            # attrs['__module__'] + '.' + attribute_name is a public callable worth logging

            # XXX XXX XXX
            #if not (attrs['__module__'] + '.' + attribute_name).startswith('b2.account_info') or attribute_name != 'put_bucket_upload_url': #'set_auth_data':
            #    continue
            # XXX XXX XXX

            # collect the `only` and `skip` sets from mro
            only = getattr(attribute_value, '_trace_only', None)
            skip = getattr(attribute_value, '_trace_skip', None)
            disable = False
            for base in bases:
                base_attribute_value = getattr(base, attribute_name, None)
                if base_attribute_value is None:
                    continue  # the base class did not define this
                if hasattr(base_attribute_value, '_trace_disable'):
                    # ex. inheriting from Abstract class, where getters are marked
                    disable = True
                    break
                only_candidates = getattr(base_attribute_value, '_trace_only', None)
                if only_candidates is not None:
                    if only is not None:
                        only.update(only_candidates)
                    else:
                        only = set(only_candidates)
                skip_candidates = getattr(base_attribute_value, '_trace_skip', None)
                if skip_candidates is not None:
                    if skip is not None:
                        skip.update(skip_candidates)
                    else:
                        skip = set(skip_candidates)

            if disable:
                continue  # the base class does not wish to trace it at all

            # create a wrapper (decorator object)
            wrapper = trace_call(
                target_logger,
                only=only,
                skip=skip,
            )
            # wrap the callable in it
            wrapped_value = wrapper(attribute_value)
            # and substitute the log-wrapped method for the original
            attrs[attribute_name] = wrapped_value
        return type.__new__(mcs, name, bases, attrs)


if __name__ == '__main__':
    import logging
    logger = logging.getLogger(__name__)
    logger.setLevel(logging.DEBUG)

    def inner():
        @trace_call(logger)
        def foo(a, b, c=None):
            return True

        foo(1, 2, 3)
        foo(a=1, b=2)
        print('+' * 70)

        @six.add_metaclass(TracePublicCallsMeta)
        class Ala(object):
            #@limit_trace_arguments(only=EMPTY_TUPLE)
            @limit_trace_arguments(only=['self', 'a', 'b'], skip=['a'])

            #@limit_trace_arguments(skip=['a'])
            #@limit_trace_arguments(only=['a'])
            #@disable_trace
            def bar(self, a, b, c=None):
                return True

        a = Ala()
        a.bar(1, 2, 3)
        a.bar(a=1, b=2)

        print('+' * 70)

        class Bela(Ala):
            def bar(self, a, b, c=None):
                return False

        b = Bela()
        b.bar(1, 2, 3)
        b.bar(a=1, b=2)

    inner()
