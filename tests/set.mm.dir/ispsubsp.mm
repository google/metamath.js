include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "psubspset.mm"
include "eleq2d.mm"
include "cvv.mm"
include "catm.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "adantr.mm"
include "wceq.mm"
include "sseq1.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem ispsubsp
  let cA: class A
  let cD: class D
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vs: setvar s
  let vx: setvar x
  assume psubspset.l: |- .<_ = ( le ` K )
  assume psubspset.j: |- .\/ = ( join ` K )
  assume psubspset.a: |- A = ( Atoms ` K )
  assume psubspset.s: |- S = ( PSubSp ` K )

  disjoint A r
  disjoint p q
  disjoint p r
  disjoint K p
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint k r
  disjoint k s
  disjoint A k
  disjoint r s
  disjoint A s
  disjoint k p
  disjoint k q
  disjoint K k
  disjoint p s
  disjoint q s
  disjoint K s
  disjoint .\/ k
  disjoint .<_ k
  disjoint A x
  disjoint K x
  disjoint .\/ x
  disjoint .<_ x
  disjoint p x
  disjoint q x
  disjoint r x
  disjoint X x
  assert |- ( K e. D -> ( X e. S <-> ( X C_ A /\ A. p e. X A. q e. X A. r e. A ( r .<_ ( p .\/ q ) -> r e. X ) ) ) )

  proof
    cK
    cD
    wcel
    #
    cX
    cS
    wcel
    cX
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    vp
    cv
    vq
    cv
    c.or
    co
    c.le
    wbr
    #
    @3
    @1
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    @1
    wral
    #
    vp
    @1
    wral
    #
    wa
    #
    vx
    cab
    #
    wcel
    cX
    cA
    wss
    #
    @4
    @3
    cX
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    cX
    wral
    #
    vp
    cX
    wral
    #
    wa
    #
    @0
    cS
    @11
    cX
    cA
    cD
    cS
    c.or
    cK
    c.le
    vx
    vr
    vq
    vp
    psubspset.l
    psubspset.j
    psubspset.a
    psubspset.s
    psubspset
    eleq2d
    @10
    @18
    vx
    cX
    @12
    cX
    cvv
    wcel
    @17
    cX
    cA
    cA
    cK
    catm
    cfv
    cvv
    psubspset.a
    cK
    catm
    fvex
    eqeltri
    ssex
    adantr
    @1
    cX
    wceq
    #
    @2
    @12
    @9
    @17
    @1
    cX
    cA
    sseq1
    @8
    @16
    vp
    @1
    cX
    @7
    @15
    vq
    @1
    cX
    @19
    @6
    @14
    vr
    cA
    @19
    @5
    @13
    @4
    @1
    cX
    @3
    eleq2
    imbi2d
    ralbidv
    raleqbi1dv
    raleqbi1dv
    anbi12d
    elab3
    syl6bb
end
