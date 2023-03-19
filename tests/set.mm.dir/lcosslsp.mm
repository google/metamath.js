include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "clspn.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "clss.mm"
include "crab.mm"
include "cint.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "ellcoellss.mm"
include "3exp.mm"
include "ad2antrr.mm"
include "imp.mm"
include "elequ1.mm"
include "rspcv.mm"
include "ad2antlr.mm"
include "syld.mm"
include "ralrimiva.mm"
include "vex.mm"
include "elintrab.mm"
include "sylibr.mm"
include "wceq.mm"
include "simpll.mm"
include "elpwi.mm"
include "eqid.mm"
include "lspval.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem lcosslsp
  let cB: class B
  let cM: class M
  let cV: class V
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lspeqvlco.b: |- B = ( Base ` M )


  assert |- ( ( M e. LMod /\ V e. ~P B ) -> ( M LinCo V ) C_ ( ( LSpan ` M ) ` V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    cpw
    wcel
    #
    wa
    #
    vx
    cM
    cV
    clinco
    co
    #
    cV
    cM
    clspn
    cfv
    #
    cfv
    #
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @6
    @5
    wcel
    @2
    @7
    wa
    #
    @6
    cV
    vs
    cv
    #
    wss
    #
    vs
    cM
    clss
    cfv
    #
    crab
    cint
    #
    @5
    @8
    @10
    vx
    vs
    wel
    #
    wi
    #
    vs
    @11
    wral
    @6
    @12
    wcel
    @8
    @14
    vs
    @11
    @8
    @9
    @11
    wcel
    #
    wa
    @10
    vy
    vs
    wel
    #
    vy
    @3
    wral
    #
    @13
    @8
    @15
    @10
    @17
    wi
    #
    @0
    @15
    @18
    wi
    @1
    @7
    @0
    @15
    @10
    @17
    vy
    @9
    cM
    cV
    ellcoellss
    3exp
    ad2antrr
    imp
    @7
    @17
    @13
    wi
    @2
    @15
    @16
    @13
    vy
    @6
    @3
    vy
    vx
    vs
    elequ1
    rspcv
    ad2antlr
    syld
    ralrimiva
    @10
    vs
    @6
    @11
    vx
    vex
    elintrab
    sylibr
    @8
    @0
    cV
    cB
    wss
    #
    @5
    @12
    wceq
    @0
    @1
    @7
    simpll
    @1
    @19
    @0
    @7
    cV
    cB
    elpwi
    ad2antlr
    vs
    @11
    cV
    @4
    cB
    cM
    lspeqvlco.b
    @11
    eqid
    @4
    eqid
    lspval
    syl2anc
    eleqtrrd
    ex
    ssrdv
end
