include "cv.mm"
include "wsbc.mm"
include "cpred.mm"
include "wral.mm"
include "wcel.mm"
include "wsb.mm"
include "sbsbc.mm"
include "sbie.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "syl5bi.mm"
include "wfisg.mm"

theorem wfis2fg
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume wfis2fg.1: |- F/ y ps
  assume wfis2fg.2: |- ( y = z -> ( ph <-> ps ) )
  assume wfis2fg.3: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint R y
  disjoint R z
  assert |- ( ( R We A /\ R Se A ) -> A. y e. A ph )

  proof
    wph
    vy
    vz
    cA
    cR
    wph
    vy
    vz
    cv
    wsbc
    #
    vz
    cA
    cR
    vy
    cv
    #
    cpred
    #
    wral
    wps
    vz
    @2
    wral
    @1
    cA
    wcel
    wph
    @0
    wps
    vz
    @2
    @0
    wph
    vy
    vz
    wsb
    wps
    wph
    vy
    vz
    sbsbc
    wph
    wps
    vy
    vz
    wfis2fg.1
    wfis2fg.2
    sbie
    bitr3i
    ralbii
    wfis2fg.3
    syl5bi
    wfisg
end
