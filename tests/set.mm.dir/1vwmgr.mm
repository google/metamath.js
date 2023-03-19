include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "cdif.mm"
include "wreu.mm"
include "wral.mm"
include "wrex.mm"
include "c0.mm"
include "ral0.mm"
include "sneq.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "preq2.mm"
include "eleq1d.mm"
include "wb.mm"
include "reueq1.mm"
include "syl.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rexsng.mm"
include "mpbiri.mm"
include "adantr.mm"
include "difeq1.mm"
include "anbi2d.mm"
include "rexeqbi1dv.mm"
include "adantl.mm"
include "mpbird.mm"

theorem 1vwmgr
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let vh: setvar h
  let cE: class E
  let cV: class V
  let cX: class X

  disjoint A h
  disjoint A v
  disjoint A w
  disjoint h v
  disjoint h w
  disjoint v w
  disjoint E h
  disjoint V h
  disjoint V v
  disjoint V w
  assert |- ( ( A e. X /\ V = { A } ) -> E. h e. V A. v e. ( V \ { h } ) ( { v , h } e. E /\ E! w e. ( V \ { h } ) { v , w } e. E ) )

  proof
    cA
    cX
    wcel
    #
    cV
    cA
    csn
    #
    wceq
    #
    wa
    vv
    cv
    #
    vh
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @3
    vw
    cv
    cpr
    cE
    wcel
    #
    vw
    cV
    @4
    csn
    #
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @9
    wral
    #
    vh
    cV
    wrex
    #
    @6
    @7
    vw
    @1
    @8
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @14
    wral
    #
    vh
    @1
    wrex
    #
    @0
    @18
    @2
    @0
    @18
    @3
    cA
    cpr
    #
    cE
    wcel
    #
    @7
    vw
    @1
    @1
    cdif
    #
    wreu
    #
    wa
    #
    vv
    c0
    wral
    #
    @23
    vv
    ral0
    @17
    @24
    vh
    cA
    cX
    @4
    cA
    wceq
    #
    @16
    @23
    vv
    @14
    c0
    @25
    @14
    @21
    c0
    @25
    @8
    @1
    @1
    @4
    cA
    sneq
    difeq2d
    #
    @1
    difid
    syl6eq
    @25
    @6
    @20
    @15
    @22
    @25
    @5
    @19
    cE
    @4
    cA
    @3
    preq2
    eleq1d
    @25
    @14
    @21
    wceq
    @15
    @22
    wb
    @26
    @7
    vw
    @14
    @21
    reueq1
    syl
    anbi12d
    raleqbidv
    rexsng
    mpbiri
    adantr
    @2
    @13
    @18
    wb
    @0
    @12
    @17
    vh
    cV
    @1
    @2
    @11
    @16
    vv
    @9
    @14
    cV
    @1
    @8
    difeq1
    #
    @2
    @10
    @15
    @6
    @2
    @9
    @14
    wceq
    @10
    @15
    wb
    @27
    @7
    vw
    @9
    @14
    reueq1
    syl
    anbi2d
    raleqbidv
    rexeqbi1dv
    adantl
    mpbird
end
