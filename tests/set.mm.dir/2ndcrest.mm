include "wcel.mm"
include "c2ndc.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "is2ndc.mm"
include "simplr.mm"
include "simpll.mm"
include "tgrest.mm"
include "syl2anc.mm"
include "restbas.mm"
include "ad2antlr.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "restval.mm"
include "1stcrestlem.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "2ndci.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "impcom.mm"

theorem 2ndcrest
  let cA: class A
  let cJ: class J
  let cV: class V
  let va: setvar a
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( ( J e. 2ndc /\ A e. V ) -> ( J |`t A ) e. 2ndc )

  proof
    cA
    cV
    wcel
    #
    cJ
    c2ndc
    wcel
    #
    cJ
    cA
    crest
    co
    #
    c2ndc
    wcel
    #
    @1
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @4
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vx
    ctb
    wrex
    @0
    @3
    vx
    cJ
    is2ndc
    @0
    @8
    @3
    vx
    ctb
    @0
    @4
    ctb
    wcel
    #
    wa
    #
    @5
    @7
    @3
    @10
    @5
    wa
    #
    @6
    cA
    crest
    co
    #
    c2ndc
    wcel
    @7
    @3
    @11
    @4
    cA
    crest
    co
    #
    ctg
    cfv
    #
    @12
    c2ndc
    @11
    @9
    @0
    @14
    @12
    wceq
    @0
    @9
    @5
    simplr
    #
    @0
    @9
    @5
    simpll
    #
    cA
    @4
    ctb
    cV
    tgrest
    syl2anc
    @11
    @13
    ctb
    wcel
    #
    @13
    com
    cdom
    wbr
    @14
    c2ndc
    wcel
    @9
    @17
    @0
    @5
    cA
    @4
    restbas
    ad2antlr
    @11
    @13
    vy
    @4
    vy
    cv
    cA
    cin
    #
    cmpt
    crn
    #
    com
    cdom
    @11
    @9
    @0
    @13
    @19
    wceq
    @15
    @16
    vy
    cA
    @4
    ctb
    cV
    restval
    syl2anc
    @5
    @19
    com
    cdom
    wbr
    @10
    vy
    @4
    @18
    1stcrestlem
    adantl
    eqbrtrd
    @13
    2ndci
    syl2anc
    eqeltrrd
    @7
    @12
    @2
    c2ndc
    @6
    cJ
    cA
    crest
    oveq1
    eleq1d
    syl5ibcom
    expimpd
    rexlimdva
    syl5bi
    impcom
end
