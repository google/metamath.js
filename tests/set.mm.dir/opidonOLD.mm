include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "inss1.mm"
include "sseli.mm"
include "ismgmOLD.mm"
include "ibi.mm"
include "syl.mm"
include "wa.mm"
include "inss2.mm"
include "isexid.mm"
include "biimpd.mm"
include "sylc.mm"
include "simpl.mm"
include "ralimi.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "eqcom.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "ex.mm"
include "syld.mm"
include "syl5.mm"
include "reximdv.mm"
include "impcom.mm"
include "ralrimiva.mm"
include "foov.mm"
include "sylanbrc.mm"

theorem opidonOLD
  let cG: class G
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume opidonOLD.1: |- X = dom dom G


  assert |- ( G e. ( Magma i^i ExId ) -> G : ( X X. X ) -onto-> X )

  proof
    cG
    cmagm
    cexid
    cin
    #
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    vy
    cv
    #
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    #
    wceq
    #
    vx
    cX
    wrex
    #
    vu
    cX
    wrex
    #
    vy
    cX
    wral
    #
    @2
    cX
    cG
    wfo
    @1
    cG
    cmagm
    wcel
    #
    @3
    @0
    cmagm
    cG
    cmagm
    cexid
    inss1
    sseli
    @12
    @3
    cmagm
    cG
    cX
    opidonOLD.1
    ismgmOLD
    ibi
    syl
    @1
    @7
    @6
    wceq
    #
    @6
    @5
    cG
    co
    @6
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    #
    @11
    @1
    cG
    cexid
    wcel
    #
    @18
    @17
    @0
    cexid
    cG
    cmagm
    cexid
    inss2
    sseli
    #
    @19
    @18
    @18
    @17
    vu
    vx
    cexid
    cG
    cX
    opidonOLD.1
    isexid
    biimpd
    sylc
    @17
    @10
    vy
    cX
    @4
    cX
    wcel
    #
    @17
    @10
    @20
    @16
    @9
    vu
    cX
    @16
    @13
    vx
    cX
    wral
    #
    @20
    @9
    @15
    @13
    vx
    cX
    @13
    @14
    simpl
    ralimi
    @20
    @21
    @5
    @4
    cG
    co
    #
    @4
    wceq
    #
    @9
    @13
    @23
    vx
    @4
    cX
    @6
    @4
    wceq
    #
    @7
    @22
    @6
    @4
    @6
    @4
    @5
    cG
    oveq2
    #
    @24
    id
    eqeq12d
    rspcv
    @20
    @23
    @9
    @8
    @23
    vx
    @4
    cX
    @8
    @7
    @4
    wceq
    @24
    @23
    @4
    @7
    eqcom
    @24
    @7
    @22
    @4
    @25
    eqeq1d
    syl5bb
    rspcev
    ex
    syld
    syl5
    reximdv
    impcom
    ralrimiva
    syl
    vu
    vx
    vy
    cX
    cX
    cX
    cG
    foov
    sylanbrc
end
