include "wwe.mm"
include "wse.mm"
include "wral.mm"
include "wfisg.mm"
include "mp2an.mm"
include "rspec.mm"

theorem wfis
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume wfis.1: |- R We A
  assume wfis.2: |- R Se A
  assume wfis.3: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) [. z / y ]. ph -> ph ) )

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
    wwe
    cA
    cR
    wse
    wph
    vy
    cA
    wral
    wfis.1
    wfis.2
    wph
    vy
    vz
    cA
    cR
    wfis.3
    wfisg
    mp2an
    rspec
end
