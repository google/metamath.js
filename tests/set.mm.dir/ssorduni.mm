include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "wtr.mm"
include "word.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wrex.mm"
include "eluni2.mm"
include "wa.mm"
include "wi.mm"
include "ssel.mm"
include "onelss.mm"
include "syl6.mm"
include "anc2r.mm"
include "syl.mm"
include "ssuni.mm"
include "syl8.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "dftr3.mm"
include "sylibr.mm"
include "onelon.mm"
include "ex.mm"
include "ssrdv.mm"
include "ordon.mm"
include "trssord.mm"
include "3exp.mm"
include "mpii.mm"
include "sylc.mm"

theorem ssorduni
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ On -> Ord U. A )

  proof
    cA
    con0
    wss
    #
    cA
    cuni
    #
    wtr
    #
    @1
    con0
    wss
    #
    @1
    word
    #
    @0
    vx
    cv
    #
    @1
    wss
    #
    vx
    @1
    wral
    @2
    @0
    @6
    vx
    @1
    @5
    @1
    wcel
    #
    @5
    vy
    cv
    #
    wcel
    #
    vy
    cA
    wrex
    #
    @0
    @6
    vy
    @5
    cA
    eluni2
    #
    @0
    @9
    @6
    vy
    cA
    @0
    @8
    cA
    wcel
    #
    @9
    @5
    @8
    wss
    #
    @12
    wa
    #
    @6
    @0
    @12
    @9
    @13
    wi
    #
    wi
    @12
    @9
    @14
    wi
    wi
    @0
    @12
    @8
    con0
    wcel
    #
    @15
    cA
    con0
    @8
    ssel
    #
    @8
    @5
    onelss
    syl6
    @12
    @9
    @13
    anc2r
    syl
    @5
    @8
    cA
    ssuni
    syl8
    rexlimdv
    syl5bi
    ralrimiv
    vx
    @1
    dftr3
    sylibr
    @0
    vx
    @1
    con0
    @7
    @10
    @0
    @5
    con0
    wcel
    #
    @11
    @0
    @9
    @18
    vy
    cA
    @0
    @12
    @16
    @9
    @18
    wi
    @17
    @16
    @9
    @18
    @8
    @5
    onelon
    ex
    syl6
    rexlimdv
    syl5bi
    ssrdv
    @2
    @3
    con0
    word
    #
    @4
    ordon
    @2
    @3
    @19
    @4
    @1
    con0
    trssord
    3exp
    mpii
    sylc
end
