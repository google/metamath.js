include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cple.mm"
include "wbr.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "atbase.mm"
include "adantl.mm"
include "simpl3.mm"
include "eqid.mm"
include "lautle.mm"
include "syl22anc.mm"
include "breq1.mm"
include "sylan9bb.mm"
include "bicomd.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "lautcl.mm"
include "syl21anc.mm"
include "hlateq.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem lauteq
  let cA: class A
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let vp: setvar p
  assume lauteq.b: |- B = ( Base ` K )
  assume lauteq.a: |- A = ( Atoms ` K )
  assume lauteq.i: |- I = ( LAut ` K )

  disjoint A p
  disjoint B p
  disjoint F p
  disjoint I p
  disjoint K p
  disjoint X p
  assert |- ( ( ( K e. HL /\ F e. I /\ X e. B ) /\ A. p e. A ( F ` p ) = p ) -> ( F ` X ) = X )

  proof
    cK
    chlt
    wcel
    #
    cF
    cI
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    vp
    cA
    wral
    #
    wa
    #
    @4
    cX
    cF
    cfv
    #
    cK
    cple
    cfv
    #
    wbr
    #
    @4
    cX
    @10
    wbr
    #
    wb
    #
    vp
    cA
    wral
    #
    @9
    cX
    wceq
    #
    @3
    @7
    @14
    @3
    @6
    @13
    vp
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @6
    @13
    @17
    @6
    wa
    @12
    @11
    @17
    @12
    @5
    @9
    @10
    wbr
    #
    @6
    @11
    @17
    @0
    @1
    @4
    cB
    wcel
    #
    @2
    @12
    @18
    wb
    @0
    @1
    @2
    @16
    simpl1
    @0
    @1
    @2
    @16
    simpl2
    @16
    @19
    @3
    cA
    cB
    @4
    cK
    lauteq.b
    lauteq.a
    atbase
    adantl
    @0
    @1
    @2
    @16
    simpl3
    cB
    cF
    cI
    cK
    @10
    chlt
    @4
    cX
    lauteq.b
    @10
    eqid
    #
    lauteq.i
    lautle
    syl22anc
    @5
    @4
    @9
    @10
    breq1
    sylan9bb
    bicomd
    ex
    ralimdva
    imp
    @8
    @0
    @9
    cB
    wcel
    #
    @2
    @14
    @15
    wb
    @0
    @1
    @2
    @7
    simpl1
    #
    @8
    @0
    @1
    @2
    @21
    @22
    @0
    @1
    @2
    @7
    simpl2
    @0
    @1
    @2
    @7
    simpl3
    #
    cB
    cF
    cI
    cK
    chlt
    cX
    lauteq.b
    lauteq.i
    lautcl
    syl21anc
    @23
    cA
    cB
    cK
    @10
    @9
    cX
    vp
    lauteq.b
    @20
    lauteq.a
    hlateq
    syl3anc
    mpbid
end
