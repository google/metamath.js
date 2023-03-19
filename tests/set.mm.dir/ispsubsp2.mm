include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "ispsubsp.mm"
include "wb.mm"
include "ralcom.mm"
include "r19.23v.mm"
include "ralbii.mm"
include "bitri.mm"
include "a1i.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem ispsubsp2
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
  disjoint A p
  disjoint A q
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
  assert |- ( K e. D -> ( X e. S <-> ( X C_ A /\ A. p e. A ( E. q e. X E. r e. X p .<_ ( q .\/ r ) -> p e. X ) ) ) )

  proof
    cK
    cD
    wcel
    #
    cX
    cS
    wcel
    cX
    cA
    wss
    #
    vp
    cv
    #
    vq
    cv
    vr
    cv
    c.or
    co
    c.le
    wbr
    #
    @2
    cX
    wcel
    #
    wi
    #
    vp
    cA
    wral
    vr
    cX
    wral
    #
    vq
    cX
    wral
    #
    wa
    @1
    @3
    vr
    cX
    wrex
    #
    vq
    cX
    wrex
    @4
    wi
    #
    vp
    cA
    wral
    #
    wa
    cA
    cD
    cS
    c.or
    cK
    c.le
    cX
    vp
    vr
    vq
    psubspset.l
    psubspset.j
    psubspset.a
    psubspset.s
    ispsubsp
    @0
    @7
    @10
    @1
    @7
    @10
    wb
    @0
    @7
    @8
    @4
    wi
    #
    vp
    cA
    wral
    #
    vq
    cX
    wral
    #
    @10
    @6
    @12
    vq
    cX
    @6
    @5
    vr
    cX
    wral
    #
    vp
    cA
    wral
    @12
    @5
    vr
    vp
    cX
    cA
    ralcom
    @14
    @11
    vp
    cA
    @3
    @4
    vr
    cX
    r19.23v
    ralbii
    bitri
    ralbii
    @13
    @11
    vq
    cX
    wral
    #
    vp
    cA
    wral
    @10
    @11
    vq
    vp
    cX
    cA
    ralcom
    @15
    @9
    vp
    cA
    @8
    @4
    vq
    cX
    r19.23v
    ralbii
    bitri
    bitri
    a1i
    anbi2d
    bitrd
end
