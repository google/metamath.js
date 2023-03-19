include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccom.mm"
include "ssbrd.mm"
include "anim12d.mm"
include "eximdv.mm"
include "ssopab2dv.mm"
include "df-co.mm"
include "3sstr4g.mm"

theorem coss12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume coss12d.a: |- ( ph -> A C_ B )
  assume coss12d.c: |- ( ph -> C C_ D )


  assert |- ( ph -> ( A o. C ) C_ ( B o. D ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cC
    wbr
    #
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    @0
    @1
    cD
    wbr
    #
    @1
    @3
    cB
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    cA
    cC
    ccom
    cB
    cD
    ccom
    wph
    @6
    @10
    vx
    vz
    wph
    @5
    @9
    vy
    wph
    @2
    @7
    @4
    @8
    wph
    cC
    cD
    @0
    @1
    coss12d.c
    ssbrd
    wph
    cA
    cB
    @1
    @3
    coss12d.a
    ssbrd
    anim12d
    eximdv
    ssopab2dv
    vx
    vz
    vy
    cA
    cC
    df-co
    vx
    vz
    vy
    cB
    cD
    df-co
    3sstr4g
end
