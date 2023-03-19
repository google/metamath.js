include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "lplnbase.mm"
include "pm4.71ri.mm"
include "islpln5.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem islpln2
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vy: setvar y
  assume islpln5.b: |- B = ( Base ` K )
  assume islpln5.l: |- .<_ = ( le ` K )
  assume islpln5.j: |- .\/ = ( join ` K )
  assume islpln5.a: |- A = ( Atoms ` K )
  assume islpln5.p: |- P = ( LPlanes ` K )

  disjoint p q
  disjoint p r
  disjoint A p
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint .\/ p
  disjoint .\/ q
  disjoint .\/ r
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint .<_ p
  disjoint .<_ q
  disjoint .<_ r
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint p y
  disjoint q y
  disjoint r y
  disjoint A y
  disjoint B y
  disjoint .\/ y
  disjoint K y
  disjoint .<_ y
  disjoint X y
  assert |- ( K e. HL -> ( X e. P <-> ( X e. B /\ E. p e. A E. q e. A E. r e. A ( p =/= q /\ -. r .<_ ( p .\/ q ) /\ X = ( ( p .\/ q ) .\/ r ) ) ) ) )

  proof
    cX
    cP
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
    vr
    cv
    #
    @3
    @4
    c.or
    co
    #
    c.le
    wbr
    wn
    cX
    @6
    @5
    c.or
    co
    wceq
    w3a
    vr
    cA
    wrex
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
    cP
    cK
    cX
    islpln5.b
    islpln5.p
    lplnbase
    pm4.71ri
    @2
    @1
    @0
    @7
    cA
    cB
    cP
    c.or
    cK
    c.le
    cX
    vr
    vq
    vp
    islpln5.b
    islpln5.l
    islpln5.j
    islpln5.a
    islpln5.p
    islpln5
    pm5.32da
    syl5bb
end
