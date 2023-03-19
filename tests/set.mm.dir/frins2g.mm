include "nfv.mm"
include "frins2fg.mm"

theorem frins2g
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume frins2g.1: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )
  assume frins2g.3: |- ( y = z -> ( ph <-> ps ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint R y
  disjoint R z
  disjoint ps y
  assert |- ( ( R Fr A /\ R Se A ) -> A. y e. A ph )

  proof
    wph
    wps
    vy
    vz
    cA
    cR
    frins2g.1
    wps
    vy
    nfv
    frins2g.3
    frins2fg
end
