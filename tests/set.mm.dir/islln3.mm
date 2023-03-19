include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "wrex.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "islln4.mm"
include "cple.mm"
include "wn.mm"
include "wb.mm"
include "simpll.mm"
include "atbase.mm"
include "adantl.mm"
include "simplr.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "cal.mm"
include "hlatl.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "atncmp.mm"
include "necom.mm"
include "syl6bb.mm"
include "eqcom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem islln3
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  assume islln3.b: |- B = ( Base ` K )
  assume islln3.j: |- .\/ = ( join ` K )
  assume islln3.a: |- A = ( Atoms ` K )
  assume islln3.n: |- N = ( LLines ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint B p
  disjoint B q
  disjoint K p
  disjoint K q
  disjoint X p
  disjoint X q
  assert |- ( ( K e. HL /\ X e. B ) -> ( X e. N <-> E. p e. A E. q e. A ( p =/= q /\ X = ( p .\/ q ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cN
    wcel
    vp
    cv
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vp
    cA
    wrex
    @3
    vq
    cv
    #
    wne
    #
    cX
    @3
    @6
    c.or
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    cA
    cB
    @4
    chlt
    cK
    cN
    cX
    vp
    islln3.b
    @4
    eqid
    #
    islln3.a
    islln3.n
    islln4
    @2
    @5
    @11
    vp
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @5
    @6
    @3
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    @8
    cX
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @11
    @14
    @0
    @3
    cB
    wcel
    #
    @1
    @5
    @19
    wb
    @0
    @1
    @13
    simpll
    @13
    @20
    @2
    cA
    cB
    @3
    cK
    islln3.b
    islln3.a
    atbase
    adantl
    @0
    @1
    @13
    simplr
    cA
    cB
    @4
    c.or
    cK
    @15
    @3
    cX
    vq
    islln3.b
    @15
    eqid
    #
    islln3.j
    @12
    islln3.a
    cvrval3
    syl3anc
    @14
    @18
    @10
    vq
    cA
    @14
    @6
    cA
    wcel
    #
    wa
    #
    @16
    @7
    @17
    @9
    @23
    @16
    @6
    @3
    wne
    #
    @7
    @23
    cK
    cal
    wcel
    #
    @22
    @13
    @16
    @24
    wb
    @0
    @25
    @1
    @13
    @22
    cK
    hlatl
    ad3antrrr
    @14
    @22
    simpr
    @2
    @13
    @22
    simplr
    cA
    @6
    @3
    cK
    @15
    @21
    islln3.a
    atncmp
    syl3anc
    @6
    @3
    necom
    syl6bb
    @17
    @9
    wb
    @23
    @8
    cX
    eqcom
    a1i
    anbi12d
    rexbidva
    bitrd
    rexbidva
    bitrd
end
