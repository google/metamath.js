include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "llnbase.mm"
include "pm4.71ri.mm"
include "islln3.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem islln2
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
  assert |- ( K e. HL -> ( X e. N <-> ( X e. B /\ E. p e. A E. q e. A ( p =/= q /\ X = ( p .\/ q ) ) ) ) )

  proof
    cX
    cN
    wcel
    #
    cX
    cB
    wcel
    #
    @0
    wa
    cK
    chlt
    wcel
    #
    @1
    vp
    cv
    #
    vq
    cv
    #
    wne
    cX
    @3
    @4
    c.or
    co
    wceq
    wa
    vq
    cA
    wrex
    vp
    cA
    wrex
    #
    wa
    @0
    @1
    cB
    cK
    cN
    cX
    islln3.b
    islln3.n
    llnbase
    pm4.71ri
    @2
    @1
    @0
    @5
    cA
    cB
    c.or
    cK
    cN
    cX
    vq
    vp
    islln3.b
    islln3.j
    islln3.a
    islln3.n
    islln3
    pm5.32da
    syl5bb
end
