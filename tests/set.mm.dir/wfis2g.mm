include "nfv.mm"
include "wfis2fg.mm"

theorem wfis2g
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume wfis2g.1: |- ( y = z -> ( ph <-> ps ) )
  assume wfis2g.2: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint ps y
  disjoint R y
  disjoint R z
  assert |- ( ( R We A /\ R Se A ) -> A. y e. A ph )

  proof
    wph
    wps
    vy
    vz
    cA
    cR
    wps
    vy
    nfv
    wfis2g.1
    wfis2g.2
    wfis2fg
end
