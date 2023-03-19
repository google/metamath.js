include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "cxp.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "dmexg.mm"
include "hashge2el2dif.mm"
include "ex.mm"
include "syl.mm"
include "wceq.mm"
include "df-ne.mm"
include "cop.mm"
include "wex.mm"
include "elvv.mm"
include "difeq1.mm"
include "funeqd.mm"
include "opwo0id.mm"
include "eqcomi.mm"
include "funeqi.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "vex.mm"
include "funopdmsn.mm"
include "3expb.mm"
include "expcom.mm"
include "syl6bi.mm"
include "com23.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "impd.mm"
include "exlimivv.mm"
include "com12.mm"
include "con3d.mm"
include "rexlimivv.mm"
include "syl6.mm"
include "com13.mm"
include "imp.mm"
include "prcnel.mm"
include "pm2.61d1.mm"

theorem fundmge2nop0
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Fun ( G \ { (/) } ) /\ 2 <_ ( # ` dom G ) ) -> -. G e. ( _V X. _V ) )

  proof
    cG
    c0
    csn
    #
    cdif
    #
    wfun
    #
    c2
    cG
    cdm
    #
    chash
    cfv
    cle
    wbr
    #
    wa
    cG
    cvv
    wcel
    #
    cG
    cvv
    cvv
    cxp
    #
    wcel
    #
    wn
    #
    @2
    @4
    @5
    @8
    wi
    @5
    @4
    @2
    @8
    @5
    @4
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    vb
    @3
    wrex
    va
    @3
    wrex
    #
    @2
    @8
    wi
    #
    @5
    @3
    cvv
    wcel
    #
    @4
    @12
    wi
    cG
    cvv
    dmexg
    @14
    @4
    @12
    va
    vb
    @3
    cvv
    hashge2el2dif
    ex
    syl
    @11
    @13
    va
    vb
    @3
    @3
    @11
    @9
    @10
    wceq
    #
    wn
    #
    @9
    @3
    wcel
    #
    @10
    @3
    wcel
    #
    wa
    #
    @13
    @9
    @10
    df-ne
    @19
    @2
    @16
    @8
    @19
    @2
    @16
    @8
    wi
    @19
    @2
    wa
    #
    @7
    @15
    @7
    cG
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
    vy
    wex
    vx
    wex
    #
    @20
    @15
    vx
    vy
    cG
    elvv
    @25
    @20
    @15
    @24
    @20
    @15
    wi
    vx
    vy
    @24
    @19
    @2
    @15
    @24
    @2
    @19
    @15
    @24
    @2
    @23
    @0
    cdif
    #
    wfun
    #
    @19
    @15
    wi
    #
    @24
    @1
    @26
    cG
    @23
    @0
    difeq1
    funeqd
    @27
    @23
    wfun
    #
    @24
    @28
    @26
    @23
    @23
    @26
    @21
    @22
    opwo0id
    eqcomi
    funeqi
    @24
    @19
    @29
    @15
    @24
    @19
    @9
    @23
    cdm
    #
    wcel
    #
    @10
    @30
    wcel
    #
    wa
    #
    @29
    @15
    wi
    @24
    @17
    @31
    @18
    @32
    @24
    @3
    @30
    @9
    cG
    @23
    dmeq
    #
    eleq2d
    @24
    @3
    @30
    @10
    @34
    eleq2d
    anbi12d
    @29
    @33
    @15
    @29
    @31
    @32
    @15
    @9
    @10
    @23
    cvv
    cvv
    @21
    @22
    @23
    eqid
    vx
    vex
    vy
    vex
    funopdmsn
    3expb
    expcom
    syl6bi
    com23
    syl5bi
    sylbid
    com23
    impd
    exlimivv
    com12
    syl5bi
    con3d
    ex
    com23
    syl5bi
    rexlimivv
    syl6
    com13
    imp
    cG
    @6
    prcnel
    pm2.61d1
end
