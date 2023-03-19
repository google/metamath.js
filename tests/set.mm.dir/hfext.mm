include "chf.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "cvv.mm"
include "cdif.mm"
include "wceq.mm"
include "wn.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "hfelhf.mm"
include "stoic1b.mm"
include "adantlr.mm"
include "adantll.mm"
include "2falsed.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "biantrud.mm"
include "wal.mm"
include "cun.mm"
include "dfcleq.mm"
include "unvdif.mm"
include "raleqi.mm"
include "ralv.mm"
include "bitr2i.mm"
include "ralunb.mm"
include "3bitri.mm"
include "syl6rbbr.mm"

theorem hfext
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. Hf /\ B e. Hf ) -> ( A = B <-> A. x e. Hf ( x e. A <-> x e. B ) ) )

  proof
    cA
    chf
    wcel
    #
    cB
    chf
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wb
    #
    vx
    chf
    wral
    #
    @7
    @6
    vx
    cvv
    chf
    cdif
    #
    wral
    #
    wa
    #
    cA
    cB
    wceq
    #
    @2
    @9
    @7
    @2
    @6
    vx
    @8
    @3
    @8
    wcel
    #
    @2
    @3
    chf
    wcel
    #
    wn
    #
    @6
    @12
    @3
    cvv
    wcel
    @14
    vx
    vex
    @3
    cvv
    chf
    eldif
    mpbiran
    @2
    @14
    wa
    @4
    @5
    @0
    @14
    @4
    wn
    @1
    @4
    @0
    @13
    @3
    cA
    hfelhf
    stoic1b
    adantlr
    @1
    @14
    @5
    wn
    @0
    @5
    @1
    @13
    @3
    cB
    hfelhf
    stoic1b
    adantll
    2falsed
    sylan2b
    ralrimiva
    biantrud
    @11
    @6
    vx
    wal
    #
    @6
    vx
    chf
    @8
    cun
    #
    wral
    #
    @10
    vx
    cA
    cB
    dfcleq
    @17
    @6
    vx
    cvv
    wral
    @15
    @6
    vx
    @16
    cvv
    chf
    unvdif
    raleqi
    @6
    vx
    ralv
    bitr2i
    @6
    vx
    chf
    @8
    ralunb
    3bitri
    syl6rbbr
end
