include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wceq.mm"
include "wrex.mm"
include "lvolbase.mm"
include "pm4.71ri.mm"
include "islvol5.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem islvol2
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vy: setvar y
  assume islvol5.b: |- B = ( Base ` K )
  assume islvol5.l: |- .<_ = ( le ` K )
  assume islvol5.j: |- .\/ = ( join ` K )
  assume islvol5.a: |- A = ( Atoms ` K )
  assume islvol5.v: |- V = ( LVols ` K )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B s
  disjoint .\/ p
  disjoint .\/ q
  disjoint .\/ r
  disjoint .\/ s
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint .<_ p
  disjoint .<_ q
  disjoint .<_ r
  disjoint .<_ s
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X s
  disjoint p y
  disjoint q y
  disjoint r y
  disjoint s y
  disjoint A y
  disjoint B y
  disjoint .\/ y
  disjoint K y
  disjoint .<_ y
  disjoint X y
  assert |- ( K e. HL -> ( X e. V <-> ( X e. B /\ E. p e. A E. q e. A E. r e. A E. s e. A ( ( p =/= q /\ -. r .<_ ( p .\/ q ) /\ -. s .<_ ( ( p .\/ q ) .\/ r ) ) /\ X = ( ( ( p .\/ q ) .\/ r ) .\/ s ) ) ) ) )

  proof
    cX
    cV
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
    vs
    cv
    #
    @6
    @5
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    cX
    @8
    @7
    c.or
    co
    wceq
    wa
    vs
    cA
    wrex
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
    cK
    cV
    cX
    islvol5.b
    islvol5.v
    lvolbase
    pm4.71ri
    @2
    @1
    @0
    @9
    cA
    cB
    c.or
    cK
    c.le
    cV
    cX
    vs
    vr
    vq
    vp
    islvol5.b
    islvol5.l
    islvol5.j
    islvol5.a
    islvol5.v
    islvol5
    pm5.32da
    syl5bb
end
