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
include "hash2prde.mm"
include "ex.mm"
include "wi.mm"
include "wb.mm"
include "cvv.mm"
include "vex.mm"
include "hashprg.mm"
include "mp2an.mm"
include "a1i.mm"
include "biimpd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "sylibrd.mm"
include "impcom.mm"
include "exlimdvv.mm"
include "impbid.mm"

theorem hash2exprb
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b

  disjoint V a
  disjoint V b
  disjoint a b
  disjoint W a
  disjoint W b
  assert |- ( V e. W -> ( ( # ` V ) = 2 <-> E. a E. b ( a =/= b /\ V = { a , b } ) ) )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    #
    c2
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cV
    @3
    @4
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
    @0
    @2
    @9
    cV
    cW
    va
    vb
    hash2prde
    ex
    @0
    @8
    @2
    va
    vb
    @8
    @2
    wi
    @0
    @7
    @5
    @2
    @7
    @5
    @6
    chash
    cfv
    #
    c2
    wceq
    #
    @2
    @7
    @5
    @11
    @5
    @11
    wb
    #
    @7
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @12
    va
    vex
    vb
    vex
    @3
    @4
    cvv
    cvv
    hashprg
    mp2an
    a1i
    biimpd
    @7
    @1
    @10
    c2
    cV
    @6
    chash
    fveq2
    eqeq1d
    sylibrd
    impcom
    a1i
    exlimdvv
    impbid
end
