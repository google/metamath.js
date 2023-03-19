include "cvv.mm"
include "wcel.mm"
include "cuhgr.mm"
include "cv.mm"
include "wnel.mm"
include "cedg.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "cvtx.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "eqid.mm"
include "nbuhgr.mm"
include "adantlr.mm"
include "wn.mm"
include "df-nel.mm"
include "wel.mm"
include "prssg.mm"
include "simpl.mm"
include "syl6bir.mm"
include "ad2antlr.mm"
include "con3d.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "imp.mm"
include "ralnex.mm"
include "sylib.mm"
include "expcom.mm"
include "expd.mm"
include "impcom.mm"
include "expdimp.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "id.mm"
include "intnand.mm"
include "nbgrprc0.mm"
include "syl.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem uhgrnbgr0nb
  let ve: setvar e
  let cG: class G
  let cN: class N
  let vn: setvar n

  disjoint G e
  disjoint N e
  disjoint G n
  disjoint e n
  disjoint N n
  assert |- ( ( G e. UHGraph /\ A. e e. ( Edg ` G ) N e/ e ) -> ( G NeighbVtx N ) = (/) )

  proof
    cN
    cvv
    wcel
    #
    cG
    cuhgr
    wcel
    #
    cN
    ve
    cv
    #
    wnel
    #
    ve
    cG
    cedg
    cfv
    #
    wral
    #
    wa
    #
    cG
    cN
    cnbgr
    co
    #
    c0
    wceq
    #
    wi
    @6
    @0
    @8
    @6
    @0
    wa
    #
    @7
    cN
    vn
    cv
    #
    cpr
    @2
    wss
    #
    ve
    @4
    wrex
    #
    vn
    cG
    cvtx
    cfv
    #
    cN
    csn
    cdif
    #
    crab
    #
    c0
    @1
    @0
    @7
    @15
    wceq
    @5
    ve
    vn
    @4
    cG
    cN
    @13
    cvv
    @13
    eqid
    @4
    eqid
    nbuhgr
    adantlr
    @9
    @12
    wn
    #
    vn
    @14
    wral
    @15
    c0
    wceq
    @9
    @16
    vn
    @14
    @6
    @0
    @10
    @14
    wcel
    #
    @16
    @5
    @1
    @0
    @17
    wa
    #
    @16
    wi
    @5
    @1
    @18
    @16
    @1
    @18
    wa
    #
    @5
    @16
    @19
    @5
    wa
    @11
    wn
    #
    ve
    @4
    wral
    #
    @16
    @19
    @5
    @21
    @19
    @3
    @20
    ve
    @4
    @3
    cN
    @2
    wcel
    #
    wn
    @19
    @2
    @4
    wcel
    #
    wa
    #
    @20
    cN
    @2
    df-nel
    @24
    @11
    @22
    @18
    @11
    @22
    wi
    @1
    @23
    @18
    @11
    @22
    vn
    ve
    wel
    #
    wa
    @22
    cN
    @10
    @2
    cvv
    @14
    prssg
    @22
    @25
    simpl
    syl6bir
    ad2antlr
    con3d
    syl5bi
    ralimdva
    imp
    @11
    ve
    @4
    ralnex
    sylib
    expcom
    expd
    impcom
    expdimp
    ralrimiv
    @12
    vn
    @14
    rabeq0
    sylibr
    eqtrd
    expcom
    @0
    wn
    #
    @8
    @6
    @26
    cG
    cvv
    wcel
    #
    @0
    wa
    wn
    @8
    @26
    @0
    @27
    @26
    id
    intnand
    cG
    cN
    nbgrprc0
    syl
    a1d
    pm2.61i
end
