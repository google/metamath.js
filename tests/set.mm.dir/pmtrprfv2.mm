include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cpr.mm"
include "cfv.mm"
include "prcom.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "wceq.mm"
include "ancom.mm"
include "necom.mm"
include "anbi12i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "biimpi.mm"
include "anim2i.mm"
include "pmtrprfv.mm"
include "syl.mm"
include "syl5eqr.mm"

theorem pmtrprfv2
  let cD: class D
  let cT: class T
  let cV: class V
  let cX: class X
  let cY: class Y
  assume pmtrprfv2.t: |- T = ( pmTrsp ` D )


  assert |- ( ( D e. V /\ ( X e. D /\ Y e. D /\ X =/= Y ) ) -> ( ( T ` { X , Y } ) ` Y ) = X )

  proof
    cD
    cV
    wcel
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    cX
    cY
    wne
    #
    w3a
    #
    wa
    #
    cY
    cX
    cY
    cpr
    #
    cT
    cfv
    #
    cfv
    cY
    cY
    cX
    cpr
    #
    cT
    cfv
    #
    cfv
    #
    cX
    cY
    @9
    @7
    @8
    @6
    cT
    cY
    cX
    prcom
    fveq2i
    fveq1i
    @5
    @0
    @2
    @1
    cY
    cX
    wne
    #
    w3a
    #
    wa
    @10
    cX
    wceq
    @4
    @12
    @0
    @4
    @12
    @1
    @2
    wa
    #
    @3
    wa
    @2
    @1
    wa
    #
    @11
    wa
    @4
    @12
    @13
    @14
    @3
    @11
    @1
    @2
    ancom
    cX
    cY
    necom
    anbi12i
    @1
    @2
    @3
    df-3an
    @2
    @1
    @11
    df-3an
    3bitr4i
    biimpi
    anim2i
    cD
    cT
    cV
    cY
    cX
    pmtrprfv2.t
    pmtrprfv
    syl
    syl5eqr
end
