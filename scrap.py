#!/usr/bin/env python
#
# File: $Id: scrap.py 2015 2009-10-21 08:36:38Z scanner $
#
"""
A dirty little script that is a re-implementation of the no longer
maintained 'Scrap' c++ program. It is hard to get that working because
the 'utils.cpp' and 'utils.h' files are missing from the source
repository.

However I want to call this from my own python scripts and web service
and it does not look that complicated so I figure - just re-implement
it in Python. This gives us the ability to test scrapers in a more
system independent fashion, and a way to use scrapers inside other
frameworks that use Python.
"""

from __future__ import with_statement

# system imports
#
import sys
import re
import types
import logging
import urllib
import urllib2
import urlparse
import string
import zipfile
from StringIO import StringIO
from xml.dom.minidom import parseString, parse
from xml.parsers.expat import ExpatError

##################################################################
##################################################################
#
class NullHandler(logging.Handler):
    """
    We define a null logging handler becauase we use logging in this module
    and if someone calls us without setting up any logging handlers we do not
    want them to be confused by spurious output.
    """

    ##################################################################
    #
    def emit(self, record):
        """
        Output nothing since this is a null logging handler.
        """
        pass

# These constants represents the functions that this Scraper
# can perform.
#
FN_GET_SETTINGS              = "GetSettings"
FN_GET_EPISODE_LIST_INTERNAL = "GetEpisodeListInternal"
FN_CREATE_SEARCH_URL         = "CreateSearchURL"
FN_GET_SEARCH_RESULTS        = "GetSearchResults"
FN_GET_DETAILS               = "GetDetails"
FN_GET_EPISODE_LIST          = "GetEpisodeList"
FN_GET_EPISODE_DETAILS       = "GetEpisodeDetails"
FN_CREATE_SEARCH_RESULTS     = "CreateSearchResults"

# Regular expression used in ScraperParser.parse_expression. No need to
# keep recompiling it every time we run since it does not change.
#
#optional_re = re.compile("(.*)(\\\\\\(.*\\\\2.*)\\\\\\)(.*)")
optional_re = re.compile(r"(.*)(\\\(.*\\2.*)\\\)(.*)", re.DOTALL)

# Our re search for '!!!CLEAN!!!...!!!CLEAN!!!' and '!!!TRIM!!!...!!!TRIM!!!' bracketed
# substrings.
#
clean_re = re.compile(r'!!!CLEAN!!!((?!!!!CLEAN!!!).*?)!!!CLEAN!!!',re.DOTALL)
trim_re = re.compile(r'!!!TRIM!!!((?!!!!TRIM!!!).*?)!!!TRIM!!!',re.DOTALL)

# Our re for '$INFO[<foo>]' substitutions (where 'foo' is for now
# going to be just alnum's. These are patterns in our output that are
# replaced with the values of the settings for a specific scraper.
#
setting_re = re.compile(r'\$INFO\[(\w+)]')

##################################################################
##################################################################
#
class ScraperException(Exception):
    """
    Raised when we encounter some unexpected and uncorrectable condition in
    th eloading and initialization of our Scraper.
    """
    def __init__(self, value = "Load failure"):
        self.value = value
    def __str__(self):
        return "InitializationFailure: %s" % self.value

##################################################################
##################################################################
#
class BadURL(ScraperException):
    """
    If we get a URL that we can not parse or interpret.
    """
    def __init__(self, value = "Bad URL"):
        self.value = value
    def __str__(self):
        return "BadURL: %s" % self.value

##################################################################
##################################################################
#
class FetchFailed(ScraperException):
    """
    If our attempt to fetch something over the network failed.
    """
    def __init__(self, value = "Fetch Failed"):
        self.value = value
    def __str__(self):
        return "FetchFailed: %s" % self.value

##################################################################
##################################################################
#
class InitializationFailure(ScraperException):
    """
    Raised when we encounter some unexpected and uncorrectable condition in
    the loading and initialization of our Scraper.
    """
    def __init__(self, value = "Load failure"):
        self.value = value
    def __str__(self):
        return "InitializationFailure: %s" % self.value

##################################################################
##################################################################
#
class BadXML(ScraperException):
    """
    Raised when the XML scraper definition we get does not conform to our
    expectations.
    """
    def __init__(self, value = "Bad Scraper XML"):
        self.value = value
    def __str__(self):
        return "BadXML: %s" % self.value

# Some helper functions for navigating a DOM object.
#

####################################################################
#
def get_int_attribute(element, attr, default = 0):
    """
    Given an element that has the attribute 'attr' return the value of that
    attribute as an integer. If it that attribute does not exist or is the
    empty string, then return the passed in default value.

    This will fail with a ValueError exception if the attribute is not an
    integer or empty.

    Arguments:
    - `element`:
    - `attr`:
    """
    result = element.getAttribute(attr)
    if result == "":
        return default
    return int(result)


####################################################################
#
def try_int(data):
    """
    A helper function meant for 'get_child_data' which tries to convert
    the argument in to an integer. If it can not it passes through the
    value unmodified.

    Arguments:
    - `data`: Try to convert this to an int.
    """
    try:
        return int(data)
    except (ValueError, TypeError ):
        return data

####################################################################
#
def try_float(data):
    """
    A helper function meant for 'get_child_data' which tries to convert
    the argument in to a float. If it can not it passes through the
    value unmodified.

    Arguments:
    - `data`: Try to convert this to an float.
    """
    try:
        return float(data)
    except (ValueError, TypeError ):
        return data

####################################################################
#
def try_url(data, cache = None, base_url = None):
    """
    Like try_int() and try_float() except this tries to convert the
    string in to a URL object. If that fails it returns None.

    Arguments:
    - `data`: Hopefully a <url>foo</url> string.
    """
    if data is None:
        return data
    return ScrapeURL(data, cache = cache, base_url = base_url)

####################################################################
#
def get_child_data(node, tag_name, default = None):
    """
    A helper function -- get the data child node of the first child
    node of `node` that has the name `tag_name`. If no such node
    exists, or that node has text subnode, return the default value
    that is passed in

    We use this pattern all the time when pulling text out of dom
    where we have:

       <foo><bar>some text</bar></foo>

    where `node` passed in a handle on <foo>

    Arguments:
    - `node`: The dom tag in which we are going to look for a specific tag name
    - `tag_name`: The name of the tag we want to find.
    - `default`: The default value if we can not find the tag, or it has no
                 child data node.
    """
    n = first_child(node, tag_name)
    if n and n.firstChild:
        return n.firstChild.data
    else:
        return default

####################################################################
#
def first_child(tree, name, recurse = False):
    """
    Return the first child node with the given name. If `recurse` is
    True then we do a depth first recursion looking for nodes with the
    given name.

    Arguments:
    - `name`: name of the node to look for.
    - `recurse`: do we look through the entire tree, depth first, for this node?
    """
    name = name.lower()
    if not tree.hasChildNodes():
        return None
    for child in tree.childNodes:
        if child.nodeType != child.ELEMENT_NODE:
            continue
        if child.tagName.lower() == name:
            return child
    return None

####################################################################
#
def next_sibling(node, name):
    """
    Go through the next sibling nodes until we find one with the given name.

    Arguments:
    - `node`: The node whose siblings we are going to search.
    - `name`: The name of the node we are looking for.
    """
    while node.nextSibling is not None:
        node = node.nextSibling
        if node.nodeType == node.ELEMENT_NODE and node.tagName == name:
            return node
    return None

##################################################################
##################################################################
#
class ScrapeURL(object):
    """
    """

    ##################################################################
    #
    def __init__(self, url, cache = { }, base_url = None):
        """
        We can be called with `url` being a string or a dom element
        node. In the later case we need to parse the element node.

        `url` - The url that this object wraps.
        """
        self.base_url = base_url
        self.cache = cache
        self.use_post = False
        self.spoof_url = None
        self.cache_key = None
        self.function = None   # if the results of this URL need to be
                               # parsed by a custom function
        if type(url) in types.StringTypes:
            self.parse_string(url)
        else:
            self.parse_element(url)

        # If we have no actual url then we can not do our url cleanups
        # because they assume we have a string, so return now.
        #
        if self.url is None:
            return

        # This is not documented in any place but URL's within things like
        # movie details are sometimes relative url's.. if the url we parsed
        # out does not begin with 'http' and is not the empty string and
        # if we got a base_url passed in, then combine the url with the base
        # url.
        #
        if self.base_url and self.url != "" and self.url[0:4].lower() != "http":
            self.url = self.base_url + self.url
        return

    ##################################################################
    #
    def __str__(self):
        result = ["<ScrapeURL, url: %s" % self.url]
        if self.use_post:
            result.append("use_post: %s" % self.use_post)
        if self.spoof_url:
            result.append("spoof_url: %s" % self.spoof_url)
        if self.cache_key:
            result.append("cache: %s" % self.cache_key)
        if self.function:
            result.append("function: %s" % self.function)

        result.append(">")
        return " ".join(result)
    
    ##################################################################
    #
    def get(self):
        """
        use the url we were configured with and get its content. Return the
        content retrieved as a string.

        NOTE: We will check our cache first for the cache key if we have
              one and use that thus avoiding any network call.
        """
        # If we have a cache_key, see if there is data under that key
        # in our url cache and use that if there is.
        #
        if self.cache_key and self.cache_key in self.cache:
            return self.cache[self.cache_key]

        # If the actual URL is the empty string, and we did not have a cached
        # result for it, then we can not retrieve anything. Return None.
        #
        if self.url is None or len(self.url) == 0:
            return None

        if not self.use_post:
            # If we are NOT using 'POST' to query the URL we can create a
            # simple urllib2.Request object.
            #
            req = urllib2.Request(self.url)
        else:
            # If we ARE using 'POST' then we need to interpret the
            # parameters out of the URL and pass them as the 'data'
            # parameter to the request object we are creating. This will
            # cause 'urlopen()' to use POST to get the results.
            #
            o = urlparse.urlsplit(self.url)
            req = urllib2.Request(o.scheme + "://" + o.netloc + o.path, o.query)

        # If 'spoof_url' is NOT None, then we
        # want our request to use the 'spoof_url' as its referrer
        #
        if self.spoof_url is not None:
            req.add_header('Referer', self.spoof_url)

        # What we get from the remote site is UTF-8 so decode it in to unicode
        # and then encode that as ASCII with characters that can not be
        # represented in ASCII replaced with their XML character references.
        #
        print "Fetching data from: %s" % self.url
        f = urllib2.urlopen(req)
        content_type = f.info()['Content-Type'].lower()

        # Based on the content type we need to deal with the response
        # in various ways, like unzip, or re-encoding as ascii.
        #
        if content_type == "application/zip":
            # In zip files we extract all the individual files.
            #
            # NOTE: Since the zipfile.ZipFile class needs a file like object
            #       with the 'seek()' method we use a StringIO to hold
            #       our url result data.
            #
            result = []
            stringy = StringIO(f.read())
            z = zipfile.ZipFile(stringy, 'r')
            members = z.namelist()
            for member in members:
                result.append(z.read(member))
            z.close()
            stringy.close()

            # The way the scraper wants to work is that it gets all parts
            # of such a zip file as a single string.. so join them all
            # together (separated by a newline character, just because.)
            #
            result = "\n".join(result)
        elif content_type[0:9] == "text/xml;":
            ign,charset = content_type.split('=')

            # XXX We should just return what we get and not encode it as
            #     ascii. The end point should encode if it only wants to
            #     see a string... (or maybe we SHOULD do this..)
            #
            result = f.read().decode(charset).encode("ascii",
                                                     "xmlcharrefreplace")
        else:
            # Finally we do not know what to do with it.. just read it
            # in to a string.
            #
            result = f.read()

        f.close()
        if self.cache_key:
            self.cache[self.cache_key] = result
        return result

    ##################################################################
    #
    def parse_element(self, element):
        """
        Parse the url dom element node.

        Arguments:
        - `element`: a dom element node that we need to get a URL from.
        """
        if element.firstChild:
            self.url = element.firstChild.data
        else:
            # This happens with these 'cache' url's. Need to figure
            # out where the cache _comes from_
            #
            self.url = None

        self.spoof_url = element.getAttribute("spoof")
        if element.hasAttribute("post"):
            self.use_post = True
        self.function = element.getAttribute("function")
        self.cache_key = element.getAttribute("cache")
        return

    ##################################################################
    #
    def parse_string(self, xml_url):
        """
        We are given a string that is an xml document that we need to
        parse for it for our url arguments. If it does not parse as an
        xml document then we consider it to be the url string.

        Arguments:
        - `xml_url`: The string containing our xml URL document.
        """
        if len(xml_url) == 0:
            raise BadURL("An empty string is not a valid URL.")
        try:
            dom = parseString(xml_url).firstChild
            self.parse_element(dom)
            dom.unlink()
            dom = None
        except ExpatError:
            self.url = xml_url
        return

##################################################################
##################################################################
#
class ScraperParser(object):
    """
    A parser for xbmc/plex scraper xml files.
    """

    # How many buffers do we support. The default seems to be 9, but I
    # have seen one scraper xml file use 12, and the wiki says 9, but
    # a forum post says 20...
    #
    NUM_BUFFERS = 20

    ##################################################################
    #
    def __init__(self, xml_document, logger = logging.getLogger()):
        self.logger = logging.getLogger(logger.name + ".ScraperParser")

        self.dom = parseString(xml_document)
        self.doc = first_child(self.dom, "scraper")
        if self.doc is None:
            raise BadXML("The scraper XML document's first child is "
                         "NOT <scraper>")

        self.name = self.doc.getAttribute("name").lower()
        self.content = self.doc.getAttribute("content").lower()

        if self.name == "" or self.content == "":
            raise BadXML("The <scraper> tag must have both a 'name' and "
                         " 'content' attribute.")

        if self.content not in ("movies", "tvshows"):
            raise BadXML("The <scraper> 'content' attribute must be 'movies' "
                         "or 'tvshows'. '%s' is not recognized." % \
                         self.content)

        self.clear_buffers()

    ##################################################################
    #
    def __del__(self):
        """
        """
        self.dom.unlink()


    ##################################################################
    #
    def clear_buffers(self):
        """
        Set each parameter buffer to the empty string.

        We create one more then our number because the xml scrapers use a 1
        based array.
        """
        self.m_param = ["" for x in range(self.NUM_BUFFERS + 1)]
        return

    ##################################################################
    #
    def set_buffer(self, i, data, append = False):
        """
        Set a parameter buffer to given data. This also re-encodes the buffer
        as an ASCII string replacing unicode references that do not map with
        XML character references.

        Arguments:
        - `i`: The 1-based index of the buffer to set.
        - `data`: The data to set in to the buffer.
        - `append`: Is the data appended to the buffer (True) or does it
                    replace the contents of the buffer (False)
        """
        if i not in range(1, self.NUM_BUFFERS + 1):
            raise IndexError("Error: Could not set buffer %d. Must be "
                             "between 1 and 9" % i)
        if type(data) == types.UnicodeType:
            data = data.encode('ascii', 'xmlcharrefreplace')
        if append:
            self.logger.debug("set_buffer(%d), appending: %s" % (i,data))
            self.m_param[i] += data
        else:
            self.logger.debug("set_buffer(%d): %s" % (i,data))
            self.m_param[i] = data
        return

    ##################################################################
    #
    def get_buffer(self, i):
        """
        Return the value of the buffer at the given index.

        Note: index is 1-based..

        Arguments:
        - `i`: 1-based index of parameter buffer to return.
        """

        if i not in range(1, self.NUM_BUFFERS + 1):
            raise IndexError("Error: Could not get buffer %d. Must be "
                             "between 1 and 9" % i)
        return self.m_param[i]

    ##################################################################
    #
    def replace_buffers(self, dest):
        """
        In the string `dest` replace all occurrences of `$$1` through
        `$$<n>` (where n == NUM_BUFFERS) with the contents of the
        self.m_param list (where $$1 == self.m_param[0])

        We also replace occurrences of the three character string
        `\\n` with an actual newline (`\n`) Return the resulting string.

        Arguments:
        - `dest`: string to carry out replacements on.
        """
        self.logger.debug("replace_buffers: dest string: '%s'" % dest)

        # To keep things simpler we convert everything to simple
        # strings, keeping intact unicode characters by replacing them
        # with their XML character references.
        #
        if type(dest) == types.UnicodeType:
            result = dest.encode('ascii', 'xmlcharrefreplace')
        else:
            result = dest

        # We need to run through the list of parameter buffers backwards
        # because we need to substitute $$10 before we substitute for $$1.
        #
        for i in range(self.NUM_BUFFERS, -1, -1):
            buff = self.m_param[i]
            if type(buff) == types.UnicodeType:
                buff = buff.encode('ascii', 'xmlcharrefreplace')
            result = result.replace("$$%d" % i, buff)

        self.logger.debug("replace_buffers: after replace: '%s'" % result)
        result = result.replace(r'\\n', '\n')

        # And replace our $INFO[<foo>] matches with their settings value.
        #
        result = setting_re.sub(self.replace_setting, result)

#         # XXX I have no idea where $INFO[url] turns in to 'imdb.com'
#         #     somewhere inside xbmc/plex I am sure..
#         #     I wish I knew where the value of this variable came from. wtf.
#         #
#         # Probably should have an 'info' dict set (with defaults) when
#         # you create the parser.
#         #
#         result = result.replace("$INFO[url]","imdb.com")
#         result = result.replace("$INFO[language]","en")

        return result

    ##################################################################
    #
    def check_condition(self, element):
        """
        <RegExp> statements may have a 'conditional' attribute. This attribute
        is a test we need to apply to see if we should or should not evaluate
        this expression.

        If the condition named in the conditional attribute is set to 'True'
        in our dict, then we return True, unless the conditional attribute
        begins with a '!' in which case we invert the logic of our test.

        If a conditional attribute does not exist in our conditions, it is the
        same as it being set to 'False'.

        Arguments:
        - `element`: The element we are checking the conditional attribute of
        """
        conditional = element.getAttribute("conditional")

        # No condition, then we execute this statement.
        #
        if len(conditional) == 0:
            return True

        # We have a conditional. See if it begins with a '!', which inverts
        # our test.
        #
        result = True
        oc = conditional
        if conditional[0] == '!':
            result = False
            conditional = conditional[1:]

        if self.settings is not None and conditional in self.settings.ids:
            if self.settings.value(conditional) is True:
                return result
            return not result
        return not result

    ##################################################################
    #
    def replace_setting(self, matchobj):
        """
        This method is intended to be called as an argument to the
        regular expression object's 'sub()' method.
        
        After we have run our data through the regular expression
        parser which builds up an XML string to return to our caller
        we need to resolve any variable references that are in the
        string.

        ie: where '$INFO[<foo>]' appears in the input string we
        replace with the value of the setting '<foo>' from our
        settings.

        If we come across a $INFO[<foo>] not in our settings we will
        raise a KeyError.

        NOTE: It is arguable that in production we should just stick
              an empty string in place of settings we do not have.
        
        Arguments:
        - `matchobj`: The re matchobj that matches our pattern
        """
        # If the first (and only) match group contains the name of the
        # setting that is going to provide the value to replace.
        #
        return self.settings.values[matchobj.group(1)]

    ##################################################################
    #
    def parse_expression(self, regexp_elt):
        """

        NOTE: The 'output' of this function is the side effect of running the
              'replace_buffers()' method, the input being the parsed and
              filled 'output' attribute format statement.

        Arguments:
        - `regexp_elt`: The <RegExp> node that we are going to process.
        """
        # The input to our expression is an attribute of the regexp node
        # which we perform a buffer replace on. This lets us feed the output
        # of other regexp's in to this one provided our caller put the correct
        # data in to the correct buffer.
        #
        # If the <RegExp> does not have an input attribute, we just snarf
        # buffer 1 for our input.
        #
        input_data = regexp_elt.getAttribute("input")
        self.logger.debug("%s++++ Entered parse expression, input='%s'" % \
                              ("  "*self.regexp_level, input_data))
        if len(input_data) > 0:
            input_data = self.replace_buffers(input_data)
        else:
            input_data = self.get_buffer(1)

        # The 'dest' attribute contains two bits of information: what buffer
        # is the data written to, and do we append new data to the buffer or
        # replace its contents.
        #
        # Think of 'dest' as the 'return value' buffer. It is where whoever
        # called this <RegExp> node wants the output of processing this
        # <RegExp> to be stored.
        #
        # If the attribute has a "+" at the end, we want to append to
        # the buffer.
        #
        # NOTE: Buffers are defined as being 1-based, not 0-based..
        #
        append = False
        dest_buffer = regexp_elt.getAttribute("dest")
        if len(dest_buffer) == 0:
            dest_buffer = 1
        else:
            if dest_buffer[-1] == "+":
                append = True
                dest_buffer = dest_buffer[:-1]
            dest_buffer = int(dest_buffer)
#             if not append:
#                 # If we are NOT appending, then we clear the buffer to make
#                 # sure that stray input does not leak to the output if we do
#                 # not actually end up setting the destination buffer in this
#                 # function.
#                 #
#                 self.set_buffer(dest_buffer, "")

        # output is our format string that describes how we want the data
        # we scrape outputted.
        #
        output_pattern = regexp_elt.getAttribute("output")
        output_pattern = self.replace_buffers(output_pattern)
        expression = first_child(regexp_elt, "expression")

        # If they have no <expression> tag then we have nothing to parse.
        #
        if not expression:
            return
        if expression.firstChild:
            str_expression = expression.firstChild.data
            str_expression = setting_re.sub(self.replace_setting,
                                             str_expression)
#             # XXX should probably have you define the language when
#             #     you create the scraper parser.
#             #
#             str_expression = str_expression.replace("$INFO[language]","en")
        else:
            str_expression = "(.*)"

        attrs = expression.attributes
        attrlist = []
        if attrs:
            for i in range(attrs.length):
                a = attrs.item(i)
                attrlist.append("%s='%s'" % (a.name, regexp_elt.getAttribute(a.name)))
        self.logger.debug("%sparse_expression, pattern: '%s', %s" % \
                              ("  "*self.regexp_level, output_pattern, ", ".join(attrlist)))
        str_expression = self.replace_buffers(str_expression)
        expression_re = re.compile(str_expression, re.DOTALL)

        # Do we match the expression just once (repeat == False)?
        #
        repeat = False
        if expression.getAttribute("repeat").lower() == "yes":
            repeat = True

        # If the expression does not matches and 'clear' is set, upon leaving
        # this function, this buffer must empty, so we just empty it now.
        #
        if expression.getAttribute("clear").lower() == "yes":
            self.set_buffer(dest_buffer, "")

        # Do we clean (strip HTML, ANSIfy, etc) the respective regexp
        # match group (by default, yes we do.)
        #
        clean = [True,True,True,True,True,True,True,True,True]
        for c in expression.getAttribute("noclean").split(','):
            if c in ('1','2','3','4','5','6','7','8','9'):
                clean[int(c)-1] = False

        # Do we trim trailing (leading too?) white space from the respective
        # regexp match group (by default, no we do not.)
        #
        trim = [False,False,False,False,False,False,False,False,False]
        for c in expression.getAttribute("trim").split(','):
            if c in ('1','2','3','4','5','6','7','8','9'):
                trim[int(c)-1] == True

        optional = get_int_attribute(expression, "optional", None)
        compare = get_int_attribute(expression, "compare", None)
        if compare:
            self.set_buffer(compare, self.get_buffer(compare).lower())

        # For every \<n> that occurs in our output string that is meant to be
        # cleaned or trimmed quote it with '!!!CLEAN!!!' and '!!!TRIM!!!'
        # respectively so that we know post processing what sections we need
        # to clean or trim.
        #
        # XXX maybe we should just 'clean' and 'trim' the replacement string
        #     when we replace \<n> with it, by passing the 'trim' and 'clean'
        #     arrays in to the 'replace_buffers()' method that does the
        #     replacements. Be a bit nicer then this hackish way of doing it.
        #
        for i_buf in range(0,8):
            temp = "\\%d" % (i_buf + 1)
            if clean[i_buf]:
                output_pattern = output_pattern.replace(temp,
                                        "!!!CLEAN!!!" + temp + "!!!CLEAN!!!")
            if trim[i_buf]:
                output_pattern = output_pattern.replace(temp,
                                        "!!!TRIM!!!" + temp + "!!!TRIM!!!")


        self.logger.debug("parse_expression: for re '%s', output pattern is: '%s'" % (str_expression, output_pattern))
        # For every match of our expression re in the current input do..
        #
        for m in expression_re.finditer(input_data):
            dbg = []
            for g in m.groups():
                if g is not None:
                    dbg.append(g[:20])
            self.logger.debug("parse_expression: matched: %s" % repr(dbg))

            # If we are not appending to our destination buffer, be sure to
            # clear it.. this is in case nothing matches and we end up not
            # setting anything in the buffer. Since we are looping, every
            # additional match we need to append (in this function)
            #
            if not append:
                self.set_buffer(dest_buffer, "")
                append = True

            # This block of code is very confusing. It basically seems to
            # remove the '\<n>'
            if optional:
                self.logger.debug("Need the optional param in buffer "
                                  "\\%d" % optional)
                param = m.expand(r'\%d' % optional)
                m2 = optional_re.search(output_pattern)
                raise NotImplemented

#                 sz_param = m.group(optional)
#                 reg2 = re.compile("(.*)(\\\\\\(.*\\\\2.*)\\\\\\)(.*)",re.DOTALL)
#                 m2 = reg2.search(output_pattern)
#                 if m2:
#                     if szParam and szParam != "":
#                         output_pattern = output_pattern[:m2.start(2)] + \
#                             output_pattern[m2.end(2):]
#                     else:
#                         # output_pattern = output_pattern
#                         # bloody confusing
#                         pass

            i_len = len(m.group(1))
            try:
                result = m.expand(output_pattern)
#                 self.logger.debug("parse_expression: result: %s" % result)
            except re.error:
                result = None
            if result is not None and len(result) > 0:
                result = self.clean(result)
                result = self.replace_buffers(result)
#                 self.logger.debug("parse_expression: after cleaning: %s" % result)
                if compare is not None:
                    if result.lower().find(self.get_buffer(compare)) != -1:
                        self.set_buffer(dest_buffer, result, append)
                else:
                    self.set_buffer(dest_buffer, result, append)

            # If repeat is not set then we exit after one iteration
            # through all the patterns that matched our regexp.
            #
            if not repeat:
                break
        self.logger.debug("parse_expression: output: buffer: %d, '%s'" % (dest_buffer,self.get_buffer(dest_buffer)))
        self.logger.debug("%s---- Leaving parse expression" % ("  "*self.regexp_level))
        return

    ##################################################################
    #
    def parse_regexp(self, regexp_elt):
        """

        Arguments:
        - `regexp_elt`:
        """

        self.regexp_level += 1
        self.logger.debug("%s^^^ entering parse_regexp" % "  "*self.regexp_level)
        # We loop over regexp_elt and its sibling <RegExp> elements
        # until there are no more.
        #
        while regexp_elt:

            # XXX Debugging
            attrs = regexp_elt.attributes
            attrlist = []
            if attrs:
                for i in range(attrs.length):
                    a = attrs.item(i)
                    attrlist.append("%s='%s'" % (a.name, regexp_elt.getAttribute(a.name)))
            self.logger.debug("%sregexp, %s" % ("  "*self.regexp_level, ", ".join(attrlist)))

            # We skip regexp's whose condition does not evaluate to True
            #
            if self.check_condition(regexp_elt):
                # If this element has a child <RegExp> element, then loop
                # over it and its sibling <RegExp> elements, performing a
                # depth-first parsing of <RegExp> elements.
                #
                child_regexp_elt = first_child(regexp_elt, "RegExp")
                if child_regexp_elt:
                    self.logger.debug("parse_regexp: recursing")
                    self.parse_regexp(child_regexp_elt)
                    self.logger.debug("parse_regexp: finished recursion")
                else:
                    child_regexp_elt = first_child(regexp_elt, "clear")
                    if child_regexp_elt:
                        self.parse_regexp(child_regexp_elt)

                # Parse this <RegExp> node..
                #
                self.parse_expression(regexp_elt)

            # And loop until we run out of sibling <RegExp> nodes.
            #
            regexp_elt = next_sibling(regexp_elt, "RegExp")
        self.logger.debug("%svvv leaving parse_regexp" % "  "*self.regexp_level)
        self.regexp_level -= 1
        return

    ##################################################################
    #
    def parse(self, tag_name, settings = None):
        """

        Arguments:
        - `tag_name`: The name of the tag we wish to parse.
        """
        self.settings = settings

        child_element = first_child(self.doc, tag_name)
        if child_element is None:
            raise BadXML("No such tag <%s>" % tag_name)

        result_buffer = get_int_attribute(child_element, "dest", 1)
        self.logger.debug("parse: Parsing tag <%s>, dest buffer: %d" % \
                          (tag_name, result_buffer))

        # Now we loop over the <RegExp> elements under <'tag_name'>
        # doing our 'prepare_parse' call on those.
        #
        # NOTE: regexp_level is entirely for debugging so we can
        #       printout how deep we are in nested <regexp>'s.
        #
        self.regexp_level = 0
        self.parse_regexp(first_child(child_element, "RegExp"))

        # our return result is the contents of the parameter buffer.
        # We clear the buffers after we are done our work.
        #
        # NOTE: 'dest' is 1-9, not 0-8
        #
        result = self.get_buffer(result_buffer)
        self.logger.debug("parse tag <%s>, result: '%s'" % (tag_name, result))

#         if child_element.getAttribute("clearbuffers").lower() != "no":
#             self.clear_buffers()
        self.clear_buffers()
        result = setting_re.sub(self.replace_setting, result)
        self.logger.debug("parse, 2nd check tag <%s>, result: '%s'" % (tag_name,result))
        return result

    ##################################################################
    #
    def clean_substr(self, match_obj):
        """
        Clean a substring by stripping out HTML and converting entity
        references to ANSI characters. Used by 'self.clean()'.

        Returns the cleaned substring.

        Arguments:
        - `match_obj`: The regexp match object whose group(1) needs to be
                       cleaned.
        """
        # XXX Right now this does nothing so we just return the
        #     the string that is meant to be cleaned.
        #
        return match_obj.group(1).strip()

    ##################################################################
    #
    def trim_substr(self, match_obj):
        """
        Trims a substring by stripping out trailing white space in the first
        match group. Used by 'self.clean()'.

        Returns the trimmed group 1 substring.

        Arguments:
        - `match_obj`: The regexp match object whose group(1) needs to be
                       trimmed.
        """
        return match_obj.group(1).strip()

    ##################################################################
    #
    def clean(self, str_dirty):
        """
        This will take a string that may have directives indicating that
        parts of it need to be 'cleaned' and 'trimmed.' We 'clean' and
        'trim' those indicated parts of the string and return the result.

        In the string there will be parts of the string quoted by
        '!!!CLEAN!!!' '!!!CLEAN!!!' and '!!!TRIM!!!' '!!!TRIM!!!.

        The substrings that are surrounded by 'CLEAN' pairs have any
        HTML in them converted to ANSI.

        The substrings that are surrounded by 'TRIM' have white space
        trimmed from their end.

        XXX I really need to find a better way to do this.. like
            cleaning and trimming the argument string before it is put
            inside our result string.

        Arguments:
        - `str_dirty`:
        """
        i = 0
        result = ""

        # See if there are any substrings that need to be cleaned.
        #
        result = clean_re.sub(self.clean_substr, str_dirty)
        result = trim_re.sub(self.trim_substr, result)

        # The regular expression only matches cases where there was a
        # non-emptry string to be cleaned and trimmed, so we do
        # another pass that just removes any "!!!CLEAN!!!!!!CLEAN!!!"
        # from the string.
        #
        result = result.replace("!!!CLEAN!!!!!!CLEAN!!!", "")
        result = result.replace("!!!TRIM!!!!!!TRIM!!!", "")

        return result

##################################################################
##################################################################
#
class Settings(object):
    """
    Scrapers can have settings. The purpose of this class is to hold
    the definition of those setting as given by the scraper so that
    other code can interrogate them for dispaly and setting in a UI.

    A setting definition has a label, id, type, value, and optionally
    a default.

    The settings object also holds the current state of the settings
    as well as their default.

    XXX I wonder if we should have a 'setting' class that is an
        individual setting instead of a settings class. I am using a
        settings class that holds all of the settings to make the
        parsing of the settings definitions and passing them around a
        little more collected.
    """

    ##################################################################
    #
    def __init__(self, settings_xml):
        """
        A settings object is initialized with the '<settings>' XML
        output of the scraper. We take this and parse it into a set of
        dictionaries that describe the settings and their values. The
        key for these dictionaries is the setting id.
        """
        # The list of setting ids.
        #
        # XXX This is redundant. We could just get the ids from
        #     getting the values of any of our dicts.
        #
        self.ids = []
        self.values = { }
        self.types = { }
        self.defaults = { }
        self.labels = { }

        dom = parseString(settings_xml)
        s = dom.firstChild

        setting = first_child(s, "setting")
        while setting:
            setting_id = setting.getAttribute("id")

            # I know the 'sep' setting has no id. I am not sure what it is used
            # for so I am just going to skip it.
            #
            if setting_id != "":
                self.ids.append(setting_id)
                self.labels[setting_id] = setting.getAttribute("label")
                self.types[setting_id] = setting.getAttribute("type")

                # For bool's actually set the default value to True or False.
                # otherwise it is all strings to us.
                #
                default = setting.getAttribute("default")
                if self.types[setting_id] == "bool":
                    self.defaults[setting_id] = (default.lower() == 'true')
                else:
                    self.defaults[setting_id] = default

                # Settings start out with their default value.
                #
                self.values[setting_id] = self.defaults[setting_id]
            setting = next_sibling(setting, "setting")

        dom.unlink()
        dom = None

        # There is always an 'override' setting - "override", which is
        # set based on the Language Override setting in the scraper.
        #
        if 'override' not in self.ids:
            self.ids.append("override")
            self.values["override"] = False
            self.types["override"] = "bool"
            self.defaults["override"] = False
            self.labels["override"] = "Language Override"

        # The default language for now is english!
        #
        if 'language' not in self.ids:
            self.ids.append("language")
            self.values["language"] = "en"
            self.types["language"] = "string"
            self.defaults["language"] = "en"
            self.labels["language"] = "Language"

        return

    ##################################################################
    #
    def value(self, setting_id):
        """
        Return the value of the given setting.

        Arguments:
        - `setting_id`: The string id for this setting. If the setting
                        does not exist we go out on a limb and return False.
        """
        if setting_id not in self.values:
            return False
        return self.values[setting_id]

    ##################################################################
    #
    def set_value(self, setting_id, value):
        """
        Set the given setting to the given value.

        NOTE: You can only set values for id's that exist.

        XXX We should do type checking on the value.

        Arguments:
        - `setting_id`: The id for the setting..
        - `value`: The value to set it to.
        """
        if setting_id not in self.values:
            raise KeyError

        if self.types[setting_id] == "bool":
            self.values[setting_id] = (value.lower() == 'true')
        else:
            self.defaults[setting_id] = value
        return

    ##################################################################
    #
    def reset(self, setting_id = None):
        """
        Reset a setting to its default value. If no id is given then all
        of the values are reset to their defaults.

        Arguments:
        - `setting_id`: The id to reset.
        """
        if setting_id is None:
            self.values = self.defaults.copy()
        else:
            self.values[setting_id] = self.defaults[setting_id]
        return

    ##################################################################
    #
    def __str__(self):
        result = []
        for setting_id in self.ids:
            result.append("id: %s, label: '%s', type: %s, default: '%s', " \
                              "value: '%s'" % (setting_id,
                                               self.labels[setting_id],
                                               self.types[setting_id],
                                               self.defaults[setting_id],
                                               self.values[setting_id]))
        return "< Setting: %s >" % "; ".join(result)

##################################################################
##################################################################
#
class Scraper(object):
    """
    The work horse object that is given an XML file, a show name, and
    what data to extract via the scraper defined in the XML file.
    """

    # Regular expressions we use precompiled here for efficiency and all that.
    #
    # NOTE: the '\+' means match a proceeding plus-sign.. which is the url
    # escaped value for the space character.
    #
    re_tags = re.compile(r"\+(ac3|custom|dc|divx|dsr|dsrip|dutch|dvd|dvdrip|dvdscr|fragment|fs|hdtv|internal|limited|multisubs|ntsc|ogg|ogm|pal|pdtv|proper|repack|rerip|retail|se|svcd|swedish|unrated|ws|xvid|xxx|cd[1-9]|\[.*\])(\+|$)")

    ##################################################################
    #
    def __init__(self, scraper_xml, logger = logging.getLogger()):
        """
        `scraper_xml` - A string that is the XML scraper we are testing.
        """
        self.logger = logging.getLogger(logger.name + ".Scraper")
        self.m_result = ""
        self.s_xml = scraper_xml
        self.parser = ScraperParser(scraper_xml, self.logger)
        self.written_data = { }

        # As we fetch data from various web resources we store
        # the results in a cache because later fetches may refer to
        # cached items to parse additional data out. No need to re-fetch
        # this from the network if we already have fetched a copy.
        #
        self.cache = { }

        # We need the settings parsed before the user does any lookups
        #
        settings_xml = self.parser.parse(FN_GET_SETTINGS)
        self.settings = Settings(settings_xml)

        return

    ##################################################################
    #
    def write_result(self, file_name):
        """
        XXX Another C++ function that can be simplified away.

        Output the contents of self.m_result in to the file with the
        given file name

        Arguments:
        - `file_name`: The name of the file to write the results in to.
        """
        f = file(file_name, "w")
        f.write(self.m_result)
        f.close()

    ##################################################################
    #
    def read_file(self, file_name):
        """
        XXX another C++ function to trivially replace in Python

        returns the contents of the given file name as a string.
        Arguments:
        - `file_name`: Name of the file to read.
        """
        f = file(file_name, "r")
        temp = f.read()
        f.close()

    ##################################################################
    #
    def custom_function(self, url, entity = None):
        """
        We are passed a ScrapeURL object that has a custom function.

        We ask the URL object for its data. If it returns any we then
        pass that in to the scraper to process via the specific function,
        if it has it (and it should because the scraper is what gave us the
        custom function to invoke.)

        If the results we get back have any <url></url>'s that also
        have a 'function' attribute then we recurse calling ourselves
        with those custom functions.

        We also pass the results of a custom function (before
        recursing) to entity object if we were passed it.  If the
        entity has a method 'fn_<foo>' where <foo> is the custom
        function we have just parsed, then we pass the results of the
        custom function to that method on the entity.

        Arguments:
        - `url`: A ScrapeURL object whose data we pass to the scraper to parse
                 via the specified custom function
        - `entity`: The entity that will parse the results of our custom
                    functions.
        """
        self.logger.debug("custom_function: '%s' entering" % url.function)

        # We must have a custom function and poking this URL for its data
        # must return some data in order for us to bother trying to parse
        # the data.
        #
        if url.function is None:
            self.logger.debug("custom_function: '%s' leaving" % url.function)
            return None

        url_data = url.get()
        if url_data is None:
            self.logger.debug("custom_function: '%s' leaving" % url.function)
            return None

        # As is usual with such things, the input data goes in to buffer
        # one of our parser.
        #
        self.parser.set_buffer(1, url_data)
        details = self.parser.parse(url.function, self.settings)

        if details is None or details == "":
            self.logger.debug("custom_function: '%s' leaving" % url.function)
            return

        dom = parseString(details)
        d = dom.firstChild

        # See if our entity knows how to deal with the results of this
        # custom function.
        #
        if entity and hasattr(entity, "fn_" + url.function):
            getattr(entity, "fn_" + url.function)(details)
        else:
            print "Entity did not support custom function '%s'" % url.function

        # Now see if we have any custom functions in our results.. if we
        # do, recurse for each one we find.
        #
        u = first_child(d, "url")
        while u:
            sub_url = ScrapeURL(u, cache = self.cache)
            self.custom_function(sub_url, entity)
            u = next_sibling(u, "url")
            
        dom.unlink()
        self.logger.debug("custom_function: '%s' leaving" % url.function)
        return

    ##################################################################
    #
    def create_search_url(self, search_string):
        """
        Arguments:
        - `search_string`: The name of the show, movie, whatever we are trying
                           to look up.
        """
        # Quote the search string so that we can pass it as an argument in a
        # query URL.
        #
        # We also treat all '.', '-', and '_' as spaces so translate those
        # to spaces before we quote.
        #
        table = string.maketrans(".-_", "   ")
        search_string = search_string.lower()
        search_string = urllib.quote_plus(search_string.translate(table))

        # If the search string matches our 'tags' regular expression, then
        # we use only what comes before tag that matched instead of the
        # entire search string.
        #
        # This is to clip off parts of file names used as search terms have
        # other bits of metadata in the file name that we do NOT want to
        # carry along, like 'dvd,'ntsc,' group names, etc.
        #
        # XXX It is this regexp we will need to enhance to work with titles
        #     that have fangroups proceeding them.
        #
        m = self.re_tags.search(search_string)
        if m:
            search_string = search_string[:m.start(1)]

        # Now, parse the <CreateSearchUrl></CreateSearchUrl> tag. We pass
        # the name of what we want the search url to search for in via
        # buffer #1.
        #
        self.parser.set_buffer(1,search_string)
        url = self.parser.parse(FN_CREATE_SEARCH_URL, self.settings)

        return url

    ##################################################################
    #
    def get_search_results(self, url):
        """
        Get the search results from some online movie/tv web service as
        specified by the URL given.

        Arguments:
        - `url`: The URL to use to search for results.
        """
        src_url = ScrapeURL(url, cache = self.cache)
        self.logger.debug("get_search_results: downloading %s" % src_url.url)
        url_data = src_url.get()

        # We pass the page we got from the url, and the url itself into
        # our scaper parser as buffer parameters 1 & 2.
        #
        self.parser.set_buffer(1, url_data)
        self.parser.set_buffer(2, src_url.url)

        # Parse the <GetSearchResults> tag from our XML definition.
        #
        search_results = self.parser.parse(FN_GET_SEARCH_RESULTS, self.settings)
        return search_results

    ##################################################################
    #
    def old_get_details(self, entity):
        """
        Get the show details based on the given search results.

        Arguments:
        - `search_results`: minidom of our search results for a term.
        """
        self.logger.debug("get_details: entered")

        # For every <url> tag that this entity has, we fetch the details it
        # provides.
        #
        link = first_child(entity, "url")
        i = 0
        while link:
            i += 1
            src_url = ScrapeURL(link, cache = self.cache)
            url_data = src_url.get()

            # If we get back an object with an iterator then we loop over the
            # elements in our src data, putting successive one in successive
            # buffers.
            #
            if hasattr(url_data, '__iter__'):
                for j,data in enumerate(url_data):
                    self.parser.set_buffer(i+j, data)
                i += j
            else:
                self.parser.set_buffer(i, url_data)
                # XXX for debugging purposes again we write out the details
                #     we get in uniquely named files that correspond to the
                #     param buffer we use for the url data.
                #
                with open("details.%d.html" % i, "w") as f:
                    f.write(url_data)


            link = next_sibling(link, "url")

        # Now we get the url based id used to identify this entity, if we
        # have one. This is passed in to the parser as the next free
        # parameter buffer.
        #
        # XXX NOTE: the xml scraper seems to always expect the id in
        #           buffer 2 (and then details html in buffer 1.)
        #
        entity_id = first_child(entity, "id")
        if entity_id is not None:
            entity_id = entity_id.firstChild.data
            self.parser.set_buffer(i+1, entity_id)
            self.logger.debug("get_details: buffer: %d entity id: %s" % \
                              (i+1,entity_id))

        details = self.parser.parse(FN_GET_DETAILS, self.settings)

        # XXX I think we only need this file for debugging. Eventually
        #     we will just remove this output statement.
        #
        with open("details.%s.xml" % entity_id, "w") as f:
            f.write(details)

        self.logger.debug("get_details: leaving")
        return details

    ##################################################################
    #
    def old_get_episode_list(self, details):
        """

        Arguments:
        - `details`:
        """
        self.logger.debug("get_episode_list: entering")

        details = parseString(details).firstChild
        dom = parseString(details)
        details = first_child(dom, "details")

        if details.firstChild.tagName != "episodeguide":
            # We do not have episode guide information for this
            # XXX Did we lookup movie info for a tv series? Probably
            #     means that this current search path should be skipped.
            #
            return []

        link = first_child(first_child(details, "episodeguide"), "url")
        episode_lists = []
        i = 0
        while link:
            i += 1
            src_url = ScrapeURL(url, cache = self.cache)
            self.logger.debug("get_episode_list: %d: %s" % (i, src_url.url))
            url_data = src_url.get()

            # XXX file exists for debugging
            #
            with open("episodelist.%d.html" % i, "w") as f:
                f.write(url_data)

            episode_lists.append(url_data)

        # We have now retrieved all of the episode lists for this series
        # One by one, pass them through our parser.
        #
        episode_list_results = []
        for i, episode_list in enumerate(episode_lists):
            self.parser.set_buffer(1, episode_list)
            episode_list_result = self.parser.parse(FN_GET_EPISODE_LIST,
                                                    self.settings)

            # XXX write retrieved parsed xml data for debugging
            #
            with open("episodelist.%d.xml" % i + 1) as f:
                f.write(episode_list_result)

            episode_list_results.append(episode_list_result)

        self.logger.debug("get_episode_list: leaving")
        return episode_list_results

    ##################################################################
    #
    def old_get_episode_details(self, episode_list_result, i):
        """

        Arguments:
        - `episode_list_result`: xml string with the episode list results
        - `i`: I think this is the 'season' but I am not positive.
        """
        self.logger.debug("get_episode_details: entered (%d)" % i)
        episode_guide = first_child(parseString(episode_list_result),
                                    "episodeguide")

        # XXX Hm.. is there a link for each episode?
        #
        link = first_child(first_child(episode_guide, "episode"), "url")
        src_url = ScrapURL(link)
        url_data = src_url.get()

        with open("episodedetails.%d.html" % i, "w") as f:
            f.write(url_data)

        self.parser.set_buffer(1, url_data)

        episode_details = self.parser.parse(FN_GET_EPISODE_DETAILS,
                                            self.settings)

        with open("episodedetails.%d.xml" % i, "w") as f:
            f.write(episode_details)

        return episode_details


    ##################################################################
    #
    def get_episode_details(self, episode):
        """
        Augment the episode object with the finer details for it.

        It returns the episode object that we update.

        Arguments:
        - `episode`: Episode object to get more details for.
        """

        url_data = episode.url.get()

        # XXX Maybe we should just not return a list because we only use
        #     the first element.
        #
        if hasattr(url_data, '__iter__'):
            url_data = url_data[0]

        self.parser.set_buffer(1, url_data)
        self.parser.set_buffer(2, episode.id)
        episode_details = self.parser.parse(FN_GET_EPISODE_DETAILS,
                                            self.settings)

        self.logger.debug("Episode details: %s" % episode_details)
        episode.set_details(episode_details)
        return episode

    ##################################################################
    #
    def get_episode_list(self, show):
        """
        we return a list of Episode objects with their basic information
        filled in.

        Arguments:
        - `show`: The Series object to get the episode list for.
        """

        # If the show has no episode guide url's, then there is nothing
        # we can fetch..
        #
        if len(show.episode_guide_urls) == 0:
            return []

        episode_list = []

        for url in show.episode_guide_urls:
            self.logger.debug("get_episode_list, data from: %s" % url.url)
            url_data = url.get()

            # Now we run the GetEpisodeList rules on this data that
            # we just retrieved.
            #
            self.parser.set_buffer(1, url_data)
            self.parser.set_buffer(2, url.url)

            # This gets us a XML string with the list of episodes in it.
            # parse this in to a dom and then go through each <episode>
            # element creating an Episode object to append to our episode
            # list
            ep_list_result = self.parser.parse(FN_GET_EPISODE_LIST,
                                               self.settings)
            dom  =parseString(ep_list_result)
            eps = dom.firstChild
            ep = first_child(eps, "episode")
            while ep:
                episode_list.append(Episode(ep, show, self))
                ep = next_sibling(ep, "episode")
            dom.unlink()
        return episode_list

#     ##################################################################
#     #
#     def get_details(self, lookup_result):
#         """
#         Get the details for the show contained in the 'lookup_result'
#         we are passed.

#         We return a Show object.

#         Arguments:
#         - `lookup_result`: The Show (Series or Movie) we are getting
#                            details for.
#         """

#         # For every URL in our lookup result, get its data and set
#         # one of the parser buffer's based on it (starting at buffer 1.)
#         #
#         i = 0
#         for link in lookup_result.links:
#             # The buffers are 1-based, so we have to start at 1.
#             #
#             i += 1
#             link_data = link.get()
#             self.logger.debug("get_details: retrieved data from %s" \
#                                   % link.url)
#             self.parser.set_buffer(i, link_data)

#         # And in the final buffer we set the id. The scraper we have
#         # loaded knows how many bits of url data it expects and in which
#         # buffer the id will be in.
#         #
#         self.logger.debug("get_details: Setting buffer %d to lookup id %s" % \
#                               (i+1, lookup_result.id))
#         self.parser.set_buffer(i+1, lookup_result.id)
#         self.logger.debug("get_details: calling Get parser")
#         details = self.parser.parse(FN_GET_DETAILS, self.settings)

#         # If this is a 'movie' type lookup, then we pass these details
#         # in to the custom function processor to suss out the movie's details
#         #
#         if self.parser.content == "movies":
#             movie_details = Movie(details, lookup_result, self)

#             # The movie details may have custom functions. If our Movie
#             # object has a method to deal with the results of a specific
#             # custom function, then invoke the custom function on the scraper
#             # then invoke that method on the Movie object.
#             #
#             for url in movie_details.urls:
#                 self.custom_function(url, movie_details)

#             return movie_details
#         else:
#             return Series(details, lookup_result, self)

    ##################################################################
    #
    def lookup(self, search_string):
        """
        Based on the search string it will find a bunch of shows/movies that
        match and return a list of search results.

        Arguments:
        - `search_string`:
        """
        url = self.create_search_url(search_string)
        self.logger.debug("lookup: using search url: %s" % url)
        search_results = self.get_search_results(url)
        results = []
        # Search results is an XML string with basic top level info about
        # all the entities that matched our search string..
        #
        dom = parseString(search_results).firstChild
        entity = first_child(dom, "entity")
        while entity:
            if self.parser.content == "movies":
                results.append(Movie(entity, self))
            else:
                results.append(Series(entity, self))
            entity = next_sibling(entity, "entity")
        return results

    ##################################################################
    #
    def old_lookup(self, search_string):
        """

        Arguments:
        - `function`:
        """
        self.logger.debug("lookup: entering (search string: '%s')" % \
                          search_string)

        url = self.create_search_url(search_string)
        self.logger.debug("lookup: using search url: %s" % url)
        search_results = self.get_search_results(url)

        return []
        # Search results is an XML string with basic top level info about
        # all the entities that matched our search string.. we want to get
        # the details for each of them. We store the results in the list
        # 'all_details'.
        #
        all_details = []
        dom = parseString(search_results).firstChild
        entity = first_child(dom, "entity")
        while entity:
            details = self.old_get_details(entity)
            if details is not None:
                all_details.append(details)
            entity = next_sibling(entity, "entity")

        for details in all_details:
            # Now based on whether we are use a XML definition for a tv show
            # (series) or a movie that determines our next step. If our XML
            # parser is for tv shows we fall in to 'get_episode_list',
            # otherwise we fall in to a 'custom' function with our details
            # as the input.
            #
            if self.parser.content == "movies":
                results.append(self.custom_functions(details))
            else:
                # Otherwise we need to get the episode lists and episode
                # details.
                #
                ep_lists = self.get_episode_list(details)

                # Now we go through the episode list results and get the
                # episode details..
                #
                results = []
                for i, ep_list in enumerate(ep_lists):
                    ep_details = self.get_episode_details(ep_list, i)
                    results.append(self.custom_functions(ep_details))

        self.logger.debug("lookup: results: %s" % repr(results))
        self.logger.debug("lookup: leaving (search: '%s')" % search_string)
        return results

##################################################################
##################################################################
#
class Show(object):
    """
    Abstract base class for movie and tv show details. They both have some
    similar methods so might as well make them share a parent base class.

    All Series and Movies have at least a title and the links to lookup the
    rest of the show's details.
    """

    ##################################################################
    #
    def __init__(self, lookup_result, scraper):
        """
        This is basically an abstract base class of both Movie and Series.
        Arguments:
        - `lookup_result`: The Dom node that has the lookup info for a
                           specific show.
        - `scraper`: The scraper used to get these details
        """
        self.scraper = scraper
        self.title = ""
        self.id = None
        self.links = []

        self.title = get_child_data(lookup_result, "title", "")
        self.id = get_child_data(lookup_result, "id", None)

        link = first_child(lookup_result, "url")
        while link:
            self.links.append(ScrapeURL(link, cache = scraper.cache))
            link = next_sibling(link, "url")
        return

    ##################################################################
    #
    def __str__(self):
        return "%s (id: %s)" % (self.title.encode("ascii","xmlcharrefreplace"),
                                self.id)

    ##################################################################
    #
    def __unicode__(self):
        return self.title

    ##################################################################
    #
    def get_details(self):
        """
        Stub function for the sub-classes to implement.
        It does the basic invoking of the parser on the data we have
        so far. Subclasses will need to extend this method to get the
        rest of the salient details.
        """
        # For every URL in our list of links that we got from the parser's
        # 'lookup()' method we get the data from that URL, set it in our
        # parser's buffer, and then let the parser do the rest of the work.
        #
        print "Show %s, id: %s.. getting details" % (self.title.encode("ascii","xmlcharrefreplace"),self.id)
        for i,link in enumerate(self.links):
            # NOTE: Buffers are 1-based, not 0-based.
            #
            link_data = link.get()
            self.scraper.parser.set_buffer(i+1, link_data)
            print "Setting buffer %d to url results: %s" % (i+1, link.url)

        # And in the final buffer we set the id. The scraper we have
        # loaded knows how many bits of url data it expects and in which
        # buffer the id will be in.
        #
        i += 1
        self.scraper.parser.set_buffer(i+1, self.id)
        print "Setting buffer %d to id %s" % (i+1, self.id)
        self.xml_details = self.scraper.parser.parse(FN_GET_DETAILS,
                                                     self.scraper.settings)
        print "Details in Show: %s" % self.xml_details
    
##################################################################
##################################################################
#
class Movie(Show):
    """
    A Movie object. As differentiated from a 'Series' object by the scraper we
    are using which tells us if it works on movies or tv shows (aka series.)
    """

    ##################################################################
    #
    def get_details(self):
        """
        Before 'get_details' is invoked this Movie object is mostly an empty
        shell. All it has is the title, maybe an id, and one or more URL's that
        will let us resolve the rest of the object.
        """
        # The basic details are put sussed out by our super class
        # method and put in 'self.xml_details'
        #
        super(Movie, self).get_details()

        # And now we get the rest of the details
        #
        self.year = ''
        self.certifications = []
        self.runtime = None
        self.rating = None
        self.votes = None
        self.genres = []
        self.directors = []
        self.writers = []
        self.studio = ''
        self.outline = ''
        self.plot = ''
        self.fanart = []   # List of URLs of fanart images.
        self.posters = []  # List of URLs of poster images.
        self.trailers = [] # List of URLs of trailers.

        # This is the list ScrapeURL's that represent custom functions
        # of further data to lookup. These, in turn, when parsed, may
        # in turn yield more custom functions to lookup more data.
        #
        self.urls = []
        
        # Further lookups for this item may only give us partial URL's
        # We take the first lookup detail link's url and use that as a
        # base url for further lookups.
        #
        self.base_url = self.links[0].url

        # And here we parse the information that was in the XML response the
        # parser gave us.
        #
        dom = parseString(self.xml_details)
        ep = dom.firstChild

        self.id = get_child_data(ep, "id", self.id)
        self.title = get_child_data(ep, "title", self.title)
        self.year = try_int(get_child_data(ep, "year"))

        certification = first_child(ep, "certification")
        while certification:
            self.certifications.append(certification.firstChild.data)
            certification = next_sibling(certification, "certification")

        self.runtime = get_child_data(ep, "runtime")
        self.rating = try_float(get_child_data(ep, "rating"))
        self.votes = try_int(get_child_data(ep, "votes"))

        genre = first_child(ep, "genre")
        while genre:
            self.genres.append(genre.firstChild.data)
            genre = next_sibling(genre, "genre")

        self.studio = get_child_data(ep, "studio", "")
        self.outline = get_child_data(ep, "outline", "")
        self.plot = get_child_data(ep, "plot", "")

        # Now we are done with the 'simple' stuff out of the XML response
        # we got from the parser. Next we loop through any "custom function"
        # URL's. These are recursive, and may also invoke back functions
        # on this movie object to fill in even more specific nested information.
        #
        url = first_child(ep, "url")
        while url:
            self.urls.append(ScrapeURL(url, cache = self.scraper.cache,
                                       base_url = self.base_url))
            url = next_sibling(url, "url")

        # At this point we are finished parsing with this dom. minidom says we
        # should still unlink it to be sure for it to be able to be GC'd. Ug.
        #
        dom.unlink()
        dom = None

        # XXX I am not sure there is any reason to store these URL's.
        #     in the above loop perhaps we should just directly invoke
        #     the parser on every URL as we come across it.
        #
        for url in self.urls:
            self.custom_function(url, self)
                
        return

    ##################################################################
    #
    def fn_GetTMDBFanart(self, details):
        """
        The handle for fanart.. <details><fanart url='..'><thumb>...
        
        Arguments:
        - `details`: XML 'GetTMDBFanart' custom function result
        """
        if details is None:
            return

        dom = parseString(details)
        d = dom.firstChild
        
        fanart = first_child(d, "fanart")
        if fanart is None:
            return

        # The 'url' attribute of the <fanart> tag is the base url for the
        # poster images and their previews. We do not store that, we just
        # construct the full urls.
        #
        url_base = fanart.getAttribute("url")

        self.fanart = []
        
        thumb = first_child(fanart, "thumb")
        while thumb:
            self.fanart.append(url_base + thumb.firstChild.data)
            thumb = next_sibling(thumb, "thumb")

        dom.unlink()
        return

    ##################################################################
    #
    def fn_GetTrailer(self, details):
        """
        Get the URL for the trailer.

        We expect: <details><trailer>..url..</trailer></details>

        <trailer> may have an attribute 'urlencoded'. If yes, then the
        trailer URL passed to us is URL encoded.

        Arguments:
        - `details`: XML string we parse for the trailer details.
        """

        if details is None:
            return

        dom = parseString(details)
        d = dom.firstChild

        self.trailers = []

        trailer = first_child(d, "trailer")
        while trailer:
            url = trailer.firstChild.data
            if trailer.getAttribute("urlencoded").lower() == "yes":
                url = urllib.unquote(url)
            self.trailers.append(url)
            trailer = next_sibling(trailer, "trailer")

        dom.unlink()
        return
    
    ##################################################################
    #
    def fn_GetMoviePlot(self, details):
        """
        The handler for the 'GetMoviePlot' scraper custom function.

        This updates any existing 'plot' we have with the more full
        details one.

        Arguments:
        - `details`: XML 'GetMoviePlot' custom function results
        """

        # If the custom url was not actually defined and we had no cached
        # data, then there is nothing to do.
        #
        if details is None:
            return

        dom = parseString(details)
        d = dom.firstChild
        self.plot = get_child_data(d, "plot", self.plot)
        dom.unlink()

    ##################################################################
    #
    def fn_GetMovieCast(self, details):
        """
        The handler for the 'GetMovieCast' scraper custom function.

        Arguments:
        - `details`: XML 'GetMovieCast' custom function results
        """

        # If the custom url was not actually defined and we had no cached
        # data, then there is nothing to do.
        #
        if details is None:
            return
        print "GetMovieCast details: %s" % details

    ##################################################################
    #
    def fn_GetMovieDirectors(self, details):
        """
        The handler for the 'GetMovieDirectors' scraper custom function.

        Arguments:
        - `details`: XML 'GetMovieDirectors' custom function results
        """

        # If the custom url was not actually defined and we had no cached
        # data, then there is nothing to do.
        #
        if details is None:
            return

        dom = parseString(details)
        e = dom.firstChild
        director = first_child(e, "director")
        while director:
            self.directors.append(director.firstChild.data)
            director = next_sibling(director, "director")
        dom.unlink()

    ##################################################################
    #
    def fn_GetMovieWriters(self, details):
        """
        The handler for the 'GetMovieWriters' scraper custom function.

        Arguments:
        - `details`: XML 'GetMovieWriters' custom function results
        """

        # If the custom url was not actually defined and we had no cached
        # data, then there is nothing to do.
        #
        if details is None:
            return

        dom = parseString(details)
        e = dom.firstChild
        credit = first_child(e, "credits")
        while credit:
            self.writers.append(credit.firstChild.data)
            credit = next_sibling(credit, "credits")
        dom.unlink()
        return

    ##################################################################
    #
    def fn_GetIMDBPoster(self, details):
        """
        The handler for the 'GetIMDBPoster' scraper custom function.
        We expect <details><thumbs><thumb>..url..</thumb><thumbs></details>
        Arguments:
        - `details`: XML 'GetIMDBPoster' custom function results
        """

        # If the custom url was not actually defined and we had no cached
        # data, then there is nothing to do.
        #
        if details is None:
            return

        dom = parseString(details)
        e = dom.firstChild
        thumbs = first_child(e, "thumbs")
        if thumbs is None:
            return
        thumb = first_child(thumbs, "thumb")
        while thumb:
            self.posters.append(thumb.firstChild.data)
            thumb = next_sibling(thumb, "thumb")
        dom.unlink()
        return

    ##################################################################
    #
    def __str__(self):
        result = []
        result.append("Title: %s" % self.title)
        result.append("year: %s" % self.year)
        if len(self.certifications) > 0:
            result.append("Certifications: %s" % ", ".join(self.certifications))
        if self.runtime:
            result.append("Runtime: %s" % self.runtime)
        if self.rating:
            result.append("Rating: %s" % self.rating)
        if self.votes:
            result.append("Votes: %s" % self.votes)
        if len(self.genres) > 0:
            result.append("Genres: %s" % ", ".join(self.genres))
        if len(self.directors) > 0:
            result.append("Directors: %s" % ", ".join(self.directors))
        if len(self.writers) > 0:
            result.append("Writers: %s" % ", ".join(self.writers))
        if len(self.posters) > 0:
            result.append("Poster URL's:")
            for p in self.posters:
                result.append("    %s" % p)
        if len(self.fanart) > 0:
            result.append("Fanart URL's:")
            for p in self.fanart:
                result.append("    %s" % p)
        if len(self.trailers) > 0:
            result.append("Trailers URL's:")
            for p in self.trailers:
                result.append("    %s" % p)
            
        result.append("Studio: %s" % self.studio)
        result.append("Outline: %s" % self.outline)
        result.append("Plot: %s" % self.plot)
        return ("\n".join(result)).encode('ascii','xmlcharrefreplace')

##################################################################
##################################################################
#
class Series(Show):
    """
    This object represents a series.. typically a TV series. It has some basic
    information about the series, and then information about each episode in
    the series.
    """

    ##################################################################
    #
    def get_details(self):
        """
        Before 'get_details' is invoked this Series object is mostly an empty
        shell. All it has is the title, maybe an id, and one or more URL's that
        will let us resolve the rest of the object.
        """
        # The basic details are put sussed out by our super class
        # method and put in 'self.xml_details'
        #
        print "Series.. getting details"
        super(Series, self).get_details()
        print "Series.. details: %s" % self.xml_details
        # And now we get the rest of the details
        #
        self.premiered = None
        self.rating = None
        self.plot = ''
        self.genres = []
        self.thumbs = []
        self.fanart = []
        self.episode_guide_urls = []

        # Further lookups for this item may only give us partial URL's
        # We take the first lookup detail link's url and use that as a
        # base url for further lookups.
        #
        self.base_url = self.links[0].url

        # XXX What we should probably do is make the Series object some sort of
        #     iterable. This way you just iterate over the episodes to get them
        #     or access them as indexed items. We can then delay the episode
        #     guide lookup and individual episode lookups until they were
        #     actually called for by the user.
        #
        self.episodes = []

        dom = parseString(self.xml_details)
        ep = dom.firstChild

        self.title = get_child_data(ep, "title", self.title)
        self.plot = get_child_data(ep, "plot", "")
        self.premiered = get_child_data(ep, "premiered")
        self.rating = try_float(get_child_data(ep, "rating"))

        genre = first_child(ep, "genre")
        while genre:
            if genre.firstChild and len(genre.firstChild.data) > 0:
                self.genres.append(genre.firstChild.data)
            genre = next_sibling(genre, "genre")

        # Thumbs have not only url's, but they can have informative attributes
        # so we store this data all as a Dict.. it will always at least have
        # the 'url' key.
        #
        thumbs = first_child(ep, "thumbs")
        if thumbs:
            thumb = first_child(thumbs, "thumb")
            while thumb:
                td = { "url" : thumb.firstChild.data }
                attrs = thumb.attributes
                for i in range(0,attrs.length):
                    attr = attrs.item(i)
                    td[attr.name] = attr.value
                self.thumbs.append(td)
                thumb = next_sibling(thumb, "thumb")

        fanart = first_child(ep, "fanart")
        if fanart:
            # The 'url' attribute of the <fanart> tag is the base url for the
            # poster images and their previews. We do not store that, we just
            # construct the full urls.
            #
            url_base = fanart.getAttribute("url")

            self.fanart = []

            thumb = first_child(fanart, "thumb")
            while thumb:
                self.fanart.append(url_base + thumb.firstChild.data)
                thumb = next_sibling(thumb, "thumb")

        episodeguide = first_child(ep, "episodeguide")
        if episodeguide:
            url = first_child(episodeguide, "url")
            while url:
                self.episode_guide_urls.append(\
                    ScrapeURL(url,cache = self.scraper.cache,
                              base_url = self.base_url))
                url = next_sibling(url, "url")

        # And at this point we have parsed out all of the series specific
        # data from our XML response, and also got a handle on where to get
        # the episode information.
        #
        dom.unlink()
        dom = None

        # Now before we return pre-emptively fetch the episode list.
        # XXX We _could_ put this in a 'get_episode_list' method that does the
        #     fetching then.. but for now we are just going to have it done
        #     here.
        #
        if len(self.episode_guide_urls) == 0:
            return

        for url in self.episode_guide_urls:
            url_data = url.get()

            # Now we run the GetEpisodeList rules on this data that
            # we just retrieved.
            #
            self.scraper.parser.set_buffer(1, url_data)
            self.scraper.parser.set_buffer(2, url.url)

            # This gets us a XML string with the list of episodes in it.
            # parse this in to a dom and then go through each <episode>
            # element creating an Episode object to append to our episode
            # list
            ep_list_result = self.scraper.parser.parse(FN_GET_EPISODE_LIST,
                                                       self.scraper.settings)
            dom = parseString(ep_list_result)
            eps = dom.firstChild
            ep = first_child(eps, "episode")
            while ep:
                self.episodes.append(Episode(ep, self, self.scraper))
                ep = next_sibling(ep, "episode")
            dom.unlink()
            dom = None
        
        return

    ##################################################################
    #
    def __unicode__(self):
        result = []
        result.append(u"Title: %s" % self.title)
        result.append("ID: %s" % self.id)
        if self.premiered:
            result.append(u"Premiered: %s" % self.premiered)
        if len(self.genres) > 0:
            result.append(u"Genres: %s" % u", ".join(self.genres))
        if self.rating:
            result.append(u"Rating: %s" % self.rating)
        result.append(u"Plot: %s" % self.plot)
        return u"\n".join(result)

    ##################################################################
    #
    def __str__(self):
        result = []
        result.append("Title: %s" % self.title.encode('ascii',
                                                      'xmlcharrefreplace'))
        result.append("ID: %s" % self.id)
        if self.premiered:
            result.append("Premiered: %s" % \
                          self.premiered.encode('ascii', 'xmlcharrefreplace'))
        if len(self.genres) > 0:
            result.append("Genres: %s" % \
                          (", ".join(self.genres)).encode('ascii',
                                                          'xmlcharrefreplace'))
        if self.rating:
            result.append("Rating: %s" % self.rating)
        result.append("Plot: %s" % self.plot.encode('ascii',
                                                    'xmlcharrefreplace'))
        return "\n".join(result)

##################################################################
##################################################################
#
class Episode(object):
    """
    A single episode of a tv series (or perhaps miniseries.)
    """

    ##################################################################
    #
    def __init__(self, episode, series, scraper):
        """
        Arguments:
        - `details`: XML string with the details of this episode
        - `series`: The series that this episode belongs to.
        - `scraper`: The scraper we are using to look this all up with.
        """
        self.details = episode.toxml("utf-8")
        self.series = series
        self.scraper = scraper
        self.url = None
        self.episode_number = None
        self.season_number = None
        self.id = None

        self.title = get_child_data(episode, "title", "")
        self.url = try_url(get_child_data(episode, "url"),
                                          cache = self.scraper.cache,
                                          base_url = self.series.base_url)
        self.episode_number = try_int(get_child_data(episode, "epnum"))
        self.season_number = try_int(get_child_data(episode, "season"))
        self.id = get_child_data(episode, "id")
        return

    ##################################################################
    #
    def __unicode__(self):
        return u"%s (S%02d%E%02d)" % (self.title, self.season_number,
                                      self.episode_number)

    ##################################################################
    #
    def __str__(self):
        return "%s (S%02dE%02d)" % (self.title.encode('ascii',
                                                      'xmlcharrefreplace'),
                                    self.season_number,self.episode_number)

    ##################################################################
    #
    def get_details(self):
        """
        Augment our existing information with these details.

        NOTE: Some of the things we set were probably already set when
              we got the episode list, and it is likely that this is
              identically retrieved information.. but it might not be
              and this is supposed to be the more details information
              so we use it.

        Arguments:
        - `details`: The XML string we parse for the details.
        """
        url_data = self.url.get()

        self.scraper.parser.set_buffer(1, url_data)
        self.scraper.parser.set_buffer(2, self.id)
        ep_details = self.scraper.parser.parse(FN_GET_EPISODE_DETAILS,
                                               self.scraper.settings)
        
        self.extended_details = ep_details
        self.actors = []
        self.credits = []

        self.scraper.logger.debug("set_details: %s" % repr(ep_details))
        dom = parseString(ep_details)
        episode = dom.firstChild

        self.title = get_child_data(episode, "title", self.title)
        self.plot = get_child_data(episode, "plot")
        self.aired = get_child_data(episode, "aired")
        self.thumbnail = get_child_data(episode, "thumb")
        self.director = get_child_data(episode, "director")
        self.rating = try_float(get_child_data(episode, "rating"))
        self.episode_number = try_int(get_child_data(episode, "episode"))
        self.season_number = try_int(get_child_data(episode, "season"))

        credit = first_child(episode, "credits")
        while credit:
            if credit.firstChild and len(credit.firstChild.data) > 0:
                self.credits.append(credit.firstChild.data)
            credit = next_sibling(credit, "credits")

        actor = first_child(episode, "actor")
        while actor:
            actor_name = get_child_data(actor, "name")
            if actor_name is not None:
                self.actors.append(actor_name)
            actor = next_sibling(actor, "actor")

        dom.unlink()
        dom = None
        return

#############################################################################
#
def main():
    """
    Main entry point for 'scrap'. Parses the arguments and then invokes our
    Scraper class.
    """
    if len(sys.argv) < 3:
        print "Error: Not enough arguments. Need a xml file, and a movie/show " \
            "name"
        print "Usage: %s imdb.xml 'Fight Club' [CreateSearchUrl]" % sys.argv[0]
        return

    logger = logging.getLogger("scraper")
    logger.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(logging.DEBUG)
    formatter = logging.Formatter("%(name)s %(levelname)s: %(message)s")
    ch.setFormatter(formatter)
    logger.addHandler(ch)

    # Create our scraper object. We pass to it our XML scraper definition
    # as a string.
    #
    f = open(sys.argv[1], 'r')
    xml = f.read()
    f.close()
    scraper = Scraper(xml, logger)

#     # If not specified the default action is 'CreateSearchURL'
#     #
#     if len(sys.argv) == 3:
#         action = FN_CREATE_SEARCH_URL
#     else:
#         action = sys.argv[3]

#     # if we are doing 'CreateSearchURL' then the movie name is placed in to
#     # buffer 1.
#     #
#     # XXX This way of passing arguments just seems so bogus. I know why it
#     #     does it this way because of the replacement strings.. but still.
#     #
#     if action == FN_CREATE_SEARCH_URL:
#         scraper.set_buffer(1, sys.argv[2])

#     scraper.parse(action)
    res = scraper.old_lookup(sys.argv[2])
    print res
    return

############################################################################
############################################################################
#
# Here is where it all starts
#
if __name__ == "__main__":
    main()
#
#
############################################################################
############################################################################
