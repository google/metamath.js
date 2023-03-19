include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crio.mm"
include "idrval.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "iorlid.mm"
include "exidu1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem cmpidelt
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vu: setvar u
  assume cmpidelt.1: |- X = ran G
  assume cmpidelt.2: |- U = ( GId ` G )


  assert |- ( ( G e. ( Magma i^i ExId ) /\ A e. X ) -> ( ( U G A ) = A /\ ( A G U ) = A ) )

  proof
    cG
    cmagm
    cexid
    cin
    #
    wcel
    #
    cU
    vx
    cv
    #
    cG
    co
    #
    @2
    wceq
    #
    @2
    cU
    cG
    co
    #
    @2
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cU
    cA
    cG
    co
    #
    cA
    wceq
    #
    cA
    cU
    cG
    co
    #
    cA
    wceq
    #
    wa
    #
    @1
    @8
    vu
    cv
    #
    @2
    cG
    co
    #
    @2
    wceq
    #
    @2
    @14
    cG
    co
    #
    @2
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
    crio
    #
    cU
    wceq
    #
    @1
    cU
    @21
    vx
    vu
    @0
    cU
    cG
    cX
    cmpidelt.1
    cmpidelt.2
    idrval
    eqcomd
    @1
    cU
    cX
    wcel
    @20
    vu
    cX
    wreu
    @8
    @22
    wb
    cU
    cG
    cX
    cmpidelt.1
    cmpidelt.2
    iorlid
    vx
    vu
    cG
    cX
    cmpidelt.1
    exidu1
    @20
    @8
    vu
    cX
    cU
    @14
    cU
    wceq
    #
    @19
    @7
    vx
    cX
    @23
    @16
    @4
    @18
    @6
    @23
    @15
    @3
    @2
    @14
    cU
    @2
    cG
    oveq1
    eqeq1d
    @23
    @17
    @5
    @2
    @14
    cU
    @2
    cG
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    riota2
    syl2anc
    mpbird
    @7
    @13
    vx
    cA
    cX
    @2
    cA
    wceq
    #
    @4
    @10
    @6
    @12
    @24
    @3
    @9
    @2
    cA
    @2
    cA
    cU
    cG
    oveq2
    @24
    id
    #
    eqeq12d
    @24
    @5
    @11
    @2
    cA
    @2
    cA
    cU
    cG
    oveq1
    @25
    eqeq12d
    anbi12d
    rspccva
    sylan
end
