include "nfv.mm"
include "frins2f.mm"

theorem frins2
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume frins2.1: |- R Fr A
  assume frins2.2: |- R Se A
  assume frins2.3: |- ( y = z -> ( ph <-> ps ) )
  assume frins2.4: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint ps y
  disjoint R y
  disjoint R z
  assert |- ( y e. A -> ph )

  proof
    wph
    wps
    vy
    vz
    cA
    cR
    frins2.1
    frins2.2
    wps
    vy
    nfv
    frins2.3
    frins2.4
    frins2f
end
