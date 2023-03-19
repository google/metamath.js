include "cres.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "wrel.mm"
include "relres.mm"
include "elrel.mm"
include "mpan.mm"
include "eleq1.mm"
include "biimpd.mm"
include "vex.mm"
include "opelres.mm"
include "biimpi.mm"
include "ancomd.mm"
include "syl6com.mm"
include "ancld.mm"
include "an12.mm"
include "syl6ib.mm"
include "2eximdv.mm"
include "mpd.mm"
include "rexcom4.mm"
include "df-rex.mm"
include "exbii.mm"
include "excom.mm"
include "3bitri.mm"
include "sylibr.mm"
include "simplbi2com.mm"
include "biimprd.mm"
include "syl9.mm"
include "impd.mm"
include "exlimdv.mm"
include "rexlimiv.mm"
include "impbii.mm"

theorem elres
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( A e. ( B |` C ) <-> E. x e. C E. y ( A = <. x , y >. /\ <. x , y >. e. B ) )

  proof
    cA
    cB
    cC
    cres
    #
    wcel
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @4
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    vx
    cC
    wrex
    #
    @1
    @2
    cC
    wcel
    #
    @7
    wa
    #
    vy
    wex
    vx
    wex
    #
    @9
    @1
    @5
    vy
    wex
    vx
    wex
    #
    @12
    @0
    wrel
    @1
    @13
    cB
    cC
    relres
    vx
    vy
    cA
    @0
    elrel
    mpan
    @1
    @5
    @11
    vx
    vy
    @1
    @5
    @5
    @10
    @6
    wa
    #
    wa
    @11
    @1
    @5
    @14
    @5
    @1
    @4
    @0
    wcel
    #
    @14
    @5
    @1
    @15
    cA
    @4
    @0
    eleq1
    #
    biimpd
    @15
    @6
    @10
    @15
    @6
    @10
    wa
    @2
    @3
    cB
    cC
    vy
    vex
    opelres
    #
    biimpi
    ancomd
    syl6com
    ancld
    @5
    @10
    @6
    an12
    syl6ib
    2eximdv
    mpd
    @9
    @7
    vx
    cC
    wrex
    #
    vy
    wex
    @11
    vx
    wex
    #
    vy
    wex
    @12
    @7
    vx
    vy
    cC
    rexcom4
    @18
    @19
    vy
    @7
    vx
    cC
    df-rex
    exbii
    @11
    vy
    vx
    excom
    3bitri
    sylibr
    @8
    @1
    vx
    cC
    @10
    @7
    @1
    vy
    @10
    @5
    @6
    @1
    @10
    @6
    @15
    @5
    @1
    @15
    @6
    @10
    @17
    simplbi2com
    @5
    @1
    @15
    @16
    biimprd
    syl9
    impd
    exlimdv
    rexlimiv
    impbii
end
