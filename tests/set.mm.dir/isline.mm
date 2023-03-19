include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "lineset.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wi.mm"
include "catm.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantl.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem isline
  let cA: class A
  let cD: class D
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vx: setvar x
  assume isline.l: |- .<_ = ( le ` K )
  assume isline.j: |- .\/ = ( join ` K )
  assume isline.a: |- A = ( Atoms ` K )
  assume isline.n: |- N = ( Lines ` K )

  disjoint p q
  disjoint p r
  disjoint A p
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint X q
  disjoint X r
  disjoint p x
  disjoint q x
  disjoint r x
  disjoint A x
  disjoint K x
  disjoint .\/ x
  disjoint .<_ x
  disjoint X x
  assert |- ( K e. D -> ( X e. N <-> E. q e. A E. r e. A ( q =/= r /\ X = { p e. A | p .<_ ( q .\/ r ) } ) ) )

  proof
    cK
    cD
    wcel
    #
    cX
    cN
    wcel
    cX
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    vx
    cv
    #
    vp
    cv
    @1
    @2
    c.or
    co
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
    vx
    cab
    #
    wcel
    @3
    cX
    @6
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
    @0
    cN
    @10
    cX
    cA
    cD
    c.or
    cK
    c.le
    cN
    vx
    vr
    vq
    vp
    isline.l
    isline.j
    isline.a
    isline.n
    lineset
    eleq2d
    @9
    @13
    vx
    cX
    @12
    cX
    cvv
    wcel
    #
    vq
    vr
    cA
    cA
    @12
    @14
    wi
    @1
    cA
    wcel
    @2
    cA
    wcel
    wa
    @11
    @14
    @3
    @11
    @14
    @6
    cvv
    wcel
    @5
    vp
    cA
    cA
    cK
    catm
    cfv
    cvv
    isline.a
    cK
    catm
    fvex
    eqeltri
    rabex
    cX
    @6
    cvv
    eleq1
    mpbiri
    adantl
    a1i
    rexlimivv
    @4
    cX
    wceq
    #
    @8
    @12
    vq
    vr
    cA
    cA
    @15
    @7
    @11
    @3
    @4
    cX
    @6
    eqeq1
    anbi2d
    2rexbidv
    elab3
    syl6bb
end
