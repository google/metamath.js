include "crn.mm"
include "wceq.mm"
include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cdm.mm"
include "rngopidOLD.mm"
include "elin.mm"
include "eqid.mm"
include "isexid.mm"
include "ibi.mm"
include "a1d.mm"
include "adantl.mm"
include "sylbi.mm"
include "eqeq2.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "com12.mm"
include "sylibrd.mm"
include "ax-mp.mm"

theorem isexid2
  let vx: setvar x
  let vu: setvar u
  let cG: class G
  let cX: class X
  assume isexid2.1: |- X = ran G

  disjoint G u
  disjoint G x
  disjoint u x
  disjoint X u
  disjoint X x
  assert |- ( G e. ( Magma i^i ExId ) -> E. u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) )

  proof
    cX
    cG
    crn
    #
    wceq
    #
    cG
    cmagm
    cexid
    cin
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    @4
    wceq
    @4
    @3
    cG
    co
    @4
    wceq
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
    wi
    isexid2.1
    @1
    @2
    @5
    vx
    @0
    wral
    #
    vu
    @0
    wrex
    #
    @7
    @2
    @1
    @9
    @0
    cG
    cdm
    cdm
    #
    wceq
    #
    @2
    @1
    @9
    wi
    #
    cG
    rngopidOLD
    @2
    @12
    @11
    cX
    @10
    wceq
    #
    @5
    vx
    @10
    wral
    #
    vu
    @10
    wrex
    #
    wi
    #
    @2
    cG
    cmagm
    wcel
    #
    cG
    cexid
    wcel
    #
    wa
    @16
    cG
    cmagm
    cexid
    elin
    @18
    @16
    @17
    @18
    @15
    @13
    @18
    @15
    vu
    vx
    cexid
    cG
    @10
    @10
    eqid
    isexid
    ibi
    a1d
    adantl
    sylbi
    @11
    @1
    @13
    @9
    @15
    @0
    @10
    cX
    eqeq2
    @8
    @14
    vu
    @0
    @10
    @5
    vx
    @0
    @10
    raleq
    rexeqbi1dv
    imbi12d
    syl5ibr
    mpcom
    com12
    @6
    @8
    vu
    cX
    @0
    @5
    vx
    cX
    @0
    raleq
    rexeqbi1dv
    sylibrd
    ax-mp
end
