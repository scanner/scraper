#!/usr/bin/env python
#
# File: $Id$
#
# XXX Provide a better docstring.
"""
The scraper package. This defines the classes and functions of our scraper.
"""

# Really we are just providing a package of the 'scrap' module. This
# is mostly so that we can add the XML scrapers as package data.
#
from scraper.scrap import *

# XXX We want to provide a list of defines scrapers as a dictionary of some
#     sort here, and have the Scraper able to take a name to lookup in this
#     dict.. OR provide a file path to an xml scraper definition.
#
