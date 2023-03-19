include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "ispsubsp2.mm"
include "simplbda.mm"
include "ex.mm"
include "wceq.mm"
include "breq1.mm"
include "2rexbidv.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl6.mm"
include "3imp1.mm"

theorem psubspi
  let cA: class A
  let cD: class D
  let cP: class P
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vk: setvar k
  let vs: setvar s
  let vp: setvar p
  let vx: setvar x
  assume psubspset.l: |- .<_ = ( le ` K )
  assume psubspset.j: |- .\/ = ( join ` K )
  assume psubspset.a: |- A = ( Atoms ` K )
  assume psubspset.s: |- S = ( PSubSp ` K )

  disjoint A r
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint X q
  disjoint X r
  disjoint A q
  disjoint P q
  disjoint P r
  disjoint k r
  disjoint k s
  disjoint A k
  disjoint r s
  disjoint A s
  disjoint k p
  disjoint k q
  disjoint K k
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint K p
  disjoint q s
  disjoint K s
  disjoint .\/ k
  disjoint .<_ k
  disjoint A x
  disjoint K x
  disjoint .\/ x
  disjoint .<_ x
  disjoint p x
  disjoint X p
  disjoint q x
  disjoint r x
  disjoint X x
  disjoint A p
  disjoint .\/ p
  disjoint .<_ p
  disjoint P p
  assert |- ( ( ( K e. D /\ X e. S /\ P e. A ) /\ E. q e. X E. r e. X P .<_ ( q .\/ r ) ) -> P e. X )

  proof
    cK
    cD
    wcel
    #
    cX
    cS
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    vq
    cv
    vr
    cv
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    cX
    wrex
    vq
    cX
    wrex
    #
    cP
    cX
    wcel
    #
    @0
    @1
    vp
    cv
    #
    @3
    c.le
    wbr
    #
    vr
    cX
    wrex
    vq
    cX
    wrex
    #
    @7
    cX
    wcel
    #
    wi
    #
    vp
    cA
    wral
    #
    @2
    @5
    @6
    wi
    #
    wi
    @0
    @1
    @12
    @0
    @1
    cX
    cA
    wss
    @12
    cA
    cD
    cS
    c.or
    cK
    c.le
    cX
    vr
    vq
    vp
    psubspset.l
    psubspset.j
    psubspset.a
    psubspset.s
    ispsubsp2
    simplbda
    ex
    @11
    @13
    vp
    cP
    cA
    @7
    cP
    wceq
    #
    @9
    @5
    @10
    @6
    @14
    @8
    @4
    vq
    vr
    cX
    cX
    @7
    cP
    @3
    c.le
    breq1
    2rexbidv
    @7
    cP
    cX
    eleq1
    imbi12d
    rspccv
    syl6
    3imp1
end
