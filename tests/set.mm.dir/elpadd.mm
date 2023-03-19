include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wo.mm"
include "wa.mm"
include "paddval.mm"
include "eleq2d.mm"
include "elun.mm"
include "wceq.mm"
include "breq1.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "orbi12i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem elpadd
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vq: setvar q
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint q r
  disjoint K q
  disjoint K r
  disjoint X q
  disjoint Y q
  disjoint Y r
  disjoint S q
  disjoint S r
  disjoint h m
  disjoint h n
  disjoint h p
  disjoint h s
  disjoint A h
  disjoint m n
  disjoint m p
  disjoint m s
  disjoint A m
  disjoint n p
  disjoint n s
  disjoint A n
  disjoint p s
  disjoint A p
  disjoint A s
  disjoint .\/ h
  disjoint h q
  disjoint h r
  disjoint K h
  disjoint m q
  disjoint m r
  disjoint K m
  disjoint n q
  disjoint n r
  disjoint K n
  disjoint p q
  disjoint p r
  disjoint K p
  disjoint q s
  disjoint r s
  disjoint K s
  disjoint .<_ h
  disjoint .\/ m
  disjoint .\/ n
  disjoint .\/ s
  disjoint .<_ m
  disjoint .<_ n
  disjoint .<_ s
  disjoint X m
  disjoint X n
  disjoint X p
  disjoint X s
  disjoint Y m
  disjoint Y n
  disjoint Y p
  disjoint Y s
  disjoint .\/ p
  disjoint .<_ p
  disjoint S p
  assert |- ( ( K e. B /\ X C_ A /\ Y C_ A ) -> ( S e. ( X .+ Y ) <-> ( ( S e. X \/ S e. Y ) \/ ( S e. A /\ E. q e. X E. r e. Y S .<_ ( q .\/ r ) ) ) ) )

  proof
    cK
    cB
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    #
    cS
    cX
    cY
    c.pl
    co
    #
    wcel
    cS
    cX
    cY
    cun
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
    #
    c.le
    wbr
    #
    vr
    cY
    wrex
    vq
    cX
    wrex
    #
    vp
    cA
    crab
    #
    cun
    #
    wcel
    #
    cS
    cX
    wcel
    cS
    cY
    wcel
    wo
    #
    cS
    cA
    wcel
    cS
    @4
    c.le
    wbr
    #
    vr
    cY
    wrex
    vq
    cX
    wrex
    #
    wa
    #
    wo
    #
    @0
    @1
    @8
    cS
    cA
    cB
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    vr
    vq
    vp
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    paddval
    eleq2d
    @9
    cS
    @2
    wcel
    #
    cS
    @7
    wcel
    #
    wo
    @14
    cS
    @2
    @7
    elun
    @15
    @10
    @16
    @13
    cS
    cX
    cY
    elun
    @6
    @12
    vp
    cS
    cA
    @3
    cS
    wceq
    @5
    @11
    vq
    vr
    cX
    cY
    @3
    cS
    @4
    c.le
    breq1
    2rexbidv
    elrab
    orbi12i
    bitri
    syl6bb
end
