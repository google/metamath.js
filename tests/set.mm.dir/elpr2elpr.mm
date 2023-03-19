include "wcel.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "simprr.mm"
include "wb.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "preq1.mm"
include "eqcoms.mm"
include "adantr.mm"
include "rspcedvd.mm"
include "ex.mm"
include "simprl.mm"
include "prcom.mm"
include "syl6eq.mm"
include "jaoi.mm"
include "elpri.mm"
include "syl11.mm"
include "3impia.mm"

theorem elpr2elpr
  let cA: class A
  let cV: class V
  let cX: class X
  let cY: class Y
  let vb: setvar b

  disjoint A b
  disjoint V b
  disjoint X b
  disjoint Y b
  assert |- ( ( X e. V /\ Y e. V /\ A e. { X , Y } ) -> E. b e. V { X , Y } = { A , b } )

  proof
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    cA
    cX
    cY
    cpr
    #
    wcel
    #
    @2
    cA
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    #
    cA
    cX
    wceq
    #
    cA
    cY
    wceq
    #
    wo
    @0
    @1
    wa
    #
    @7
    @3
    @8
    @10
    @7
    wi
    @9
    @8
    @10
    @7
    @8
    @10
    wa
    #
    @6
    @2
    cA
    cY
    cpr
    #
    wceq
    #
    vb
    cY
    cV
    @8
    @0
    @1
    simprr
    @4
    cY
    wceq
    #
    @6
    @13
    wb
    @11
    @14
    @5
    @12
    @2
    @4
    cY
    cA
    preq2
    eqeq2d
    adantl
    @8
    @13
    @10
    @13
    cX
    cA
    cX
    cA
    cY
    preq1
    eqcoms
    adantr
    rspcedvd
    ex
    @9
    @10
    @7
    @9
    @10
    wa
    #
    @6
    @2
    cA
    cX
    cpr
    #
    wceq
    #
    vb
    cX
    cV
    @9
    @0
    @1
    simprl
    @4
    cX
    wceq
    #
    @6
    @17
    wb
    @15
    @18
    @5
    @16
    @2
    @4
    cX
    cA
    preq2
    eqeq2d
    adantl
    @9
    @17
    @10
    @9
    @2
    cX
    cA
    cpr
    #
    @16
    @2
    @19
    wceq
    cY
    cA
    cY
    cA
    cX
    preq2
    eqcoms
    cX
    cA
    prcom
    syl6eq
    adantr
    rspcedvd
    ex
    jaoi
    cA
    cX
    cY
    elpri
    syl11
    3impia
end
