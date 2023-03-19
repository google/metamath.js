include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cvrlt.mm"
include "cple.mm"
include "cfv.mm"
include "wn.mm"
include "eqid.mm"
include "cvrval3.mm"
include "simpr.mm"
include "reximi.mm"
include "syl6bi.mm"
include "imp.mm"
include "jca.mm"
include "ex.mm"
include "simp1r.mm"
include "simp3.mm"
include "breqtrrd.mm"
include "wb.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2.mm"
include "cvr1.mm"
include "syl3anc.mm"
include "cvr2N.mm"
include "bitr4d.mm"
include "mpbird.mm"
include "3exp.mm"
include "reximdvai.mm"
include "expimpd.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem cvrval4N
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cvrval4.b: |- B = ( Base ` K )
  assume cvrval4.s: |- .< = ( lt ` K )
  assume cvrval4.j: |- .\/ = ( join ` K )
  assume cvrval4.c: |- C = ( <o ` K )
  assume cvrval4.a: |- A = ( Atoms ` K )

  disjoint .< p
  disjoint A p
  disjoint B p
  disjoint C p
  disjoint K p
  disjoint X p
  disjoint Y p
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( X .< Y /\ E. p e. A ( X .\/ p ) = Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cC
    wbr
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    vp
    cv
    #
    c.or
    co
    #
    cY
    wceq
    #
    vp
    cA
    wrex
    #
    wa
    #
    @3
    @4
    @10
    @3
    @4
    wa
    @5
    @9
    chlt
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrval4.b
    cvrval4.s
    cvrval4.c
    cvrlt
    @3
    @4
    @9
    @3
    @4
    @6
    cX
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    @8
    wa
    #
    vp
    cA
    wrex
    #
    @9
    cA
    cB
    cC
    c.or
    cK
    @11
    cX
    cY
    vp
    cvrval4.b
    @11
    eqid
    #
    cvrval4.j
    cvrval4.c
    cvrval4.a
    cvrval3
    #
    @13
    @8
    vp
    cA
    @12
    @8
    simpr
    reximi
    syl6bi
    imp
    jca
    ex
    @3
    @10
    @14
    @4
    @3
    @5
    @9
    @14
    @3
    @5
    wa
    #
    @8
    @13
    vp
    cA
    @17
    @6
    cA
    wcel
    #
    @8
    @13
    @17
    @18
    @8
    w3a
    #
    @12
    @8
    @19
    @12
    cX
    @7
    c.lt
    wbr
    #
    @19
    cX
    cY
    @7
    c.lt
    @3
    @5
    @18
    @8
    simp1r
    @17
    @18
    @8
    simp3
    #
    breqtrrd
    @19
    @12
    cX
    @7
    cC
    wbr
    #
    @20
    @19
    @0
    @1
    @18
    @12
    @22
    wb
    @0
    @1
    @2
    @5
    @18
    @8
    simp1l1
    #
    @0
    @1
    @2
    @5
    @18
    @8
    simp1l2
    #
    @17
    @18
    @8
    simp2
    #
    cA
    cB
    cC
    @6
    c.or
    cK
    @11
    cX
    cvrval4.b
    @15
    cvrval4.j
    cvrval4.c
    cvrval4.a
    cvr1
    syl3anc
    @19
    @0
    @1
    @18
    @20
    @22
    wb
    @23
    @24
    @25
    cA
    cB
    cC
    @6
    c.lt
    c.or
    cK
    cX
    cvrval4.b
    cvrval4.s
    cvrval4.j
    cvrval4.c
    cvrval4.a
    cvr2N
    syl3anc
    bitr4d
    mpbird
    @21
    jca
    3exp
    reximdvai
    expimpd
    @16
    sylibrd
    impbid
end
