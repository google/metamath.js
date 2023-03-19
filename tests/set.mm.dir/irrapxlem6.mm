include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cdenom.mm"
include "c2.mm"
include "cneg.mm"
include "cexp.mm"
include "w3a.mm"
include "cq.mm"
include "crab.mm"
include "wrex.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpr3.mm"
include "jca.mm"
include "weq.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "simpr2.mm"
include "breq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "irrapxlem5.mm"
include "r19.29a.mm"

theorem irrapxlem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. { y e. QQ | ( 0 < y /\ ( abs ` ( y - A ) ) < ( ( denom ` y ) ^ -u 2 ) ) } ( abs ` ( x - A ) ) < B )

  proof
    cA
    crp
    wcel
    cB
    crp
    wcel
    wa
    #
    cc0
    va
    cv
    #
    clt
    wbr
    #
    @1
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    @4
    @1
    cdenom
    cfv
    #
    c2
    cneg
    #
    cexp
    co
    #
    clt
    wbr
    #
    w3a
    #
    vx
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    vx
    cc0
    vy
    cv
    #
    clt
    wbr
    #
    @15
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    cdenom
    cfv
    #
    @7
    cexp
    co
    #
    clt
    wbr
    #
    wa
    #
    vy
    cq
    crab
    #
    wrex
    #
    va
    cq
    @0
    @1
    cq
    wcel
    #
    wa
    #
    @10
    wa
    #
    @1
    @23
    wcel
    #
    @5
    @24
    @27
    @25
    @2
    @9
    wa
    #
    @28
    @0
    @25
    @10
    simplr
    @27
    @2
    @9
    @26
    @2
    @5
    @9
    simpr1
    @26
    @2
    @5
    @9
    simpr3
    jca
    @22
    @29
    vy
    @1
    cq
    vy
    va
    weq
    #
    @16
    @2
    @21
    @9
    @15
    @1
    cc0
    clt
    breq2
    @30
    @18
    @4
    @20
    @8
    clt
    @30
    @17
    @3
    cabs
    @15
    @1
    cA
    cmin
    oveq1
    fveq2d
    @30
    @19
    @6
    @7
    cexp
    @15
    @1
    cdenom
    fveq2
    oveq1d
    breq12d
    anbi12d
    elrab
    sylanbrc
    @26
    @2
    @5
    @9
    simpr2
    @14
    @5
    vx
    @1
    @23
    vx
    va
    weq
    #
    @13
    @4
    cB
    clt
    @31
    @12
    @3
    cabs
    @11
    @1
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    rspcev
    syl2anc
    va
    cA
    cB
    irrapxlem5
    r19.29a
end
