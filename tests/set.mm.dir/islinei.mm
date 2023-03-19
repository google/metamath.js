include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "neeq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "wb.mm"
include "simpl1.mm"
include "isline.mm"
include "syl.mm"
include "mpbird.mm"

theorem islinei
  let cA: class A
  let cD: class D
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vx: setvar x
  assume isline.l: |- .<_ = ( le ` K )
  assume isline.j: |- .\/ = ( join ` K )
  assume isline.a: |- A = ( Atoms ` K )
  assume isline.n: |- N = ( Lines ` K )

  disjoint A p
  disjoint K p
  disjoint Q p
  disjoint R p
  disjoint p q
  disjoint p r
  disjoint p x
  disjoint q r
  disjoint q x
  disjoint A q
  disjoint r x
  disjoint A r
  disjoint A x
  disjoint K q
  disjoint K r
  disjoint K x
  disjoint .\/ x
  disjoint .<_ x
  disjoint X q
  disjoint X r
  disjoint X x
  disjoint .\/ q
  disjoint .\/ r
  disjoint .<_ q
  disjoint .<_ r
  disjoint Q q
  disjoint Q r
  disjoint R r
  assert |- ( ( ( K e. D /\ Q e. A /\ R e. A ) /\ ( Q =/= R /\ X = { p e. A | p .<_ ( Q .\/ R ) } ) ) -> X e. N )

  proof
    cK
    cD
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cQ
    cR
    wne
    #
    cX
    vp
    cv
    #
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    vp
    cA
    crab
    #
    wceq
    #
    wa
    #
    wa
    #
    cX
    cN
    wcel
    #
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    cX
    @5
    @13
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    vp
    cA
    crab
    #
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    vq
    cA
    wrex
    #
    @11
    @1
    @2
    @10
    @21
    @0
    @1
    @2
    @10
    simpl2
    @0
    @1
    @2
    @10
    simpl3
    @3
    @10
    simpr
    @20
    @10
    cQ
    @14
    wne
    #
    cX
    @5
    cQ
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    vp
    cA
    crab
    #
    wceq
    #
    wa
    vq
    vr
    cQ
    cR
    cA
    cA
    @13
    cQ
    wceq
    #
    @15
    @22
    @19
    @26
    @13
    cQ
    @14
    neeq1
    @27
    @18
    @25
    cX
    @27
    @17
    @24
    vp
    cA
    @27
    @16
    @23
    @5
    c.le
    @13
    cQ
    @14
    c.or
    oveq1
    breq2d
    rabbidv
    eqeq2d
    anbi12d
    @14
    cR
    wceq
    #
    @22
    @4
    @26
    @9
    @14
    cR
    cQ
    neeq2
    @28
    @25
    @8
    cX
    @28
    @24
    @7
    vp
    cA
    @28
    @23
    @6
    @5
    c.le
    @14
    cR
    cQ
    c.or
    oveq2
    breq2d
    rabbidv
    eqeq2d
    anbi12d
    rspc2ev
    syl3anc
    @11
    @0
    @12
    @21
    wb
    @0
    @1
    @2
    @10
    simpl1
    cA
    cD
    c.or
    cK
    c.le
    cN
    cX
    vr
    vq
    vp
    isline.l
    isline.j
    isline.a
    isline.n
    isline
    syl
    mpbird
end
