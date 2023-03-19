include "wwe.mm"
include "wse.mm"
include "wral.mm"
include "wfis2fg.mm"
include "mp2an.mm"
include "rspec.mm"

theorem wfis2f
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume wfis2f.1: |- R We A
  assume wfis2f.2: |- R Se A
  assume wfis2f.3: |- F/ y ps
  assume wfis2f.4: |- ( y = z -> ( ph <-> ps ) )
  assume wfis2f.5: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

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
    wfis2f.1
    wfis2f.2
    wph
    wps
    vy
    vz
    cA
    cR
    wfis2f.3
    wfis2f.4
    wfis2f.5
    wfis2fg
    mp2an
    rspec
end
