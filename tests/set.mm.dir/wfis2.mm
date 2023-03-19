include "wwe.mm"
include "wse.mm"
include "wral.mm"
include "wfis2g.mm"
include "mp2an.mm"
include "rspec.mm"

theorem wfis2
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume wfis2.1: |- R We A
  assume wfis2.2: |- R Se A
  assume wfis2.3: |- ( y = z -> ( ph <-> ps ) )
  assume wfis2.4: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

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
    wfis2.1
    wfis2.2
    wph
    wps
    vy
    vz
    cA
    cR
    wfis2.3
    wfis2.4
    wfis2g
    mp2an
    rspec
end
