include "wfr.mm"
include "wse.mm"
include "wral.mm"
include "frinsg.mm"
include "mp2an.mm"
include "rspec.mm"

theorem frins
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume frins.1: |- R Fr A
  assume frins.2: |- R Se A
  assume frins.3: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) [. z / y ]. ph -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint R y
  disjoint R z
  assert |- ( y e. A -> ph )

  proof
    wph
    vy
    cA
    cA
    cR
    wfr
    cA
    cR
    wse
    wph
    vy
    cA
    wral
    frins.1
    frins.2
    wph
    vy
    vz
    cA
    cR
    frins.3
    frinsg
    mp2an
    rspec
end
