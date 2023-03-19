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
include "frinsg.mm"

theorem frins2fg
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume frins2fg.1: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )
  assume frins2fg.2: |- F/ y ps
  assume frins2fg.3: |- ( y = z -> ( ph <-> ps ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint R y
  disjoint R z
  assert |- ( ( R Fr A /\ R Se A ) -> A. y e. A ph )

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
    frins2fg.2
    frins2fg.3
    sbie
    bitr3i
    ralbii
    frins2fg.1
    syl5bi
    frinsg
end
