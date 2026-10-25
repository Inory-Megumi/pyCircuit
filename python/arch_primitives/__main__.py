"""Command line entry for architecture component source elaboration."""

import argparse
import json
from pathlib import Path

from . import elaborate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    args = parser.parse_args()
    manifest = elaborate(args.source, args.output)
    args.output.with_suffix('.components.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(str(args.output))


if __name__ == '__main__':
    main()
