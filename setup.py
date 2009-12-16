import os
from distutils.core import setup

# We package our scraper definitions along with our module. Since this list
# will change every now and then I will programatically determine what are
# current set of scrapers are.
#
scraperdir = os.path.join(os.path.dirname(__file__), 'scraper','scrapers')
package_data = []

# Walk our scraper directory looking for files which have the correct
# file postfix. We collect these in to a dict by directory.
#
for dirpath, dirnames, filenames in os.walk('scrapers'):
    for filename in filenames:
        ign, ext = os.path.splitext(filename)
        if ext.lower() in ('.xml', '.png', '.jpg', '.gif'):
            pacakge_data.append(os.path.join(dirpath, filename))

setup(name='scraper',
      version = '0.5',
      packages = ['scraper'],
      package_data = { 'scraper' : package_data},
      )
