include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "exidreslem.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl.mm"
include "wb.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "resexg.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "isexid.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem exidres
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vu: setvar u
  assume exidres.1: |- X = ran G
  assume exidres.2: |- U = ( GId ` G )
  assume exidres.3: |- H = ( G |` ( Y X. Y ) )


  assert |- ( ( G e. ( Magma i^i ExId ) /\ Y C_ X /\ U e. Y ) -> H e. ExId )

  proof
    cG
    cmagm
    cexid
    cin
    #
    wcel
    #
    cY
    cX
    wss
    #
    cU
    cY
    wcel
    #
    w3a
    #
    cH
    cexid
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    @7
    wceq
    #
    @7
    @6
    cH
    co
    #
    @7
    wceq
    #
    wa
    #
    vx
    cH
    cdm
    cdm
    #
    wral
    #
    vu
    @13
    wrex
    #
    @4
    cU
    @13
    wcel
    cU
    @7
    cH
    co
    #
    @7
    wceq
    #
    @7
    cU
    cH
    co
    #
    @7
    wceq
    #
    wa
    #
    vx
    @13
    wral
    #
    wa
    @15
    vx
    cU
    cG
    cH
    cX
    cY
    exidres.1
    exidres.2
    exidres.3
    exidreslem
    @14
    @21
    vu
    cU
    @13
    @6
    cU
    wceq
    #
    @12
    @20
    vx
    @13
    @22
    @9
    @17
    @11
    @19
    @22
    @8
    @16
    @7
    @6
    cU
    @7
    cH
    oveq1
    eqeq1d
    @22
    @10
    @18
    @7
    @6
    cU
    @7
    cH
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    syl
    @1
    @2
    @5
    @15
    wb
    #
    @3
    @1
    cH
    cvv
    wcel
    @23
    @1
    cH
    cG
    cY
    cY
    cxp
    #
    cres
    cvv
    exidres.3
    cG
    @24
    @0
    resexg
    syl5eqel
    vu
    vx
    cvv
    cH
    @13
    @13
    eqid
    isexid
    syl
    3ad2ant1
    mpbird
end
