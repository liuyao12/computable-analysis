# Hydrogen fine structure showpiece

The deployed destination is
<https://liuyao12.github.io/computable-analysis/hydrogen/>.

The page states the dimensionless Dirac–Coulomb model, the constructed regular
channel energies and original closed-graph eigenpairs, and exact remainder inequalities for the two featured gaps
and their ratio. Its convenient common cap is \(0<\alpha\leq1/16\).
Individual theorem ranges are also displayed. It distinguishes the established
regular channel and closed-relation results from the open unrestricted Cartesian operator theorem.

`sources/` contains selected actual statement source snapshots, hashed in
`source-manifest.json`. These are not a standalone dependency bundle.
`statement-check.lean` inspects fourteen existing declarations;
`statement-audit.txt` records their axiom reports. It does not certify a fresh
aggregate repository build.

The manually dispatched `publish_hydrogen_showpiece.yml` workflow uses
`scripts/publish_hydrogen_showpiece.py`. Because Pages artifacts expire, it
preserves the live site using the prior complete file inventory and discovered
static references, verifies the index did not change during the snapshot,
and adds the showpiece and one home page link. It checks that every other
downloaded file remains byte identical. It never builds unrelated working
tree mathematics. `hydrogen/publication.json` records the preserved hashes.

For a local publication check, supply an output directory and optionally the
downloaded inventory path:

```sh
python3 scripts/publish_hydrogen_showpiece.py /tmp/hydrogen-site /tmp/pages-base.json
```
