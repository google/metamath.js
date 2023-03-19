include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "hash2exprb.mm"
include "wb.mm"
include "vex.mm"
include "prid1.mm"
include "prid2.mm"
include "pm3.2i.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "mpbiri.mm"
include "adantl.mm"
include "pm4.71ri.mm"
include "2exbii.mm"
include "a1i.mm"
include "r2ex.mm"
include "bicomi.mm"
include "3bitrd.mm"

theorem hash2prb
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b

  disjoint V a
  disjoint V b
  disjoint a b
  disjoint W a
  disjoint W b
  assert |- ( V e. W -> ( ( # ` V ) = 2 <-> E. a e. V E. b e. V ( a =/= b /\ V = { a , b } ) ) )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    c2
    wceq
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cV
    @1
    @2
    cpr
    #
    wceq
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    @1
    cV
    wcel
    #
    @2
    cV
    wcel
    #
    wa
    #
    @6
    wa
    #
    vb
    wex
    va
    wex
    #
    @6
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    cV
    cW
    va
    vb
    hash2exprb
    @7
    @12
    wb
    @0
    @6
    @11
    va
    vb
    @6
    @10
    @5
    @10
    @3
    @5
    @10
    @1
    @4
    wcel
    #
    @2
    @4
    wcel
    #
    wa
    @14
    @15
    @1
    @2
    va
    vex
    prid1
    @1
    @2
    vb
    vex
    prid2
    pm3.2i
    @5
    @8
    @14
    @9
    @15
    cV
    @4
    @1
    eleq2
    cV
    @4
    @2
    eleq2
    anbi12d
    mpbiri
    adantl
    pm4.71ri
    2exbii
    a1i
    @12
    @13
    wb
    @0
    @13
    @12
    @6
    va
    vb
    cV
    cV
    r2ex
    bicomi
    a1i
    3bitrd
end
