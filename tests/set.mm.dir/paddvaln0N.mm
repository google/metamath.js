include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "elpaddn0.mm"
include "weq.mm"
include "breq1.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem paddvaln0N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let cS: class S
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint A p
  disjoint p q
  disjoint p r
  disjoint K p
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint X p
  disjoint X q
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint .\/ p
  disjoint .<_ p
  disjoint A q
  disjoint A r
  disjoint .\/ q
  disjoint .\/ r
  disjoint .<_ q
  disjoint .<_ r
  disjoint X r
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
  disjoint X s
  disjoint Y m
  disjoint Y n
  disjoint Y s
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint .+ s
  assert |- ( ( ( K e. Lat /\ X C_ A /\ Y C_ A ) /\ ( X =/= (/) /\ Y =/= (/) ) ) -> ( X .+ Y ) = { p e. A | E. q e. X E. r e. Y p .<_ ( q .\/ r ) } )

  proof
    cK
    clat
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    cX
    c0
    wne
    cY
    c0
    wne
    wa
    wa
    #
    vs
    cX
    cY
    c.pl
    co
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
    @0
    vs
    cv
    #
    @1
    wcel
    @7
    cA
    wcel
    @7
    @3
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
    @7
    @6
    wcel
    cA
    c.pl
    @7
    c.or
    cK
    c.le
    cX
    cY
    vr
    vq
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpaddn0
    @5
    @9
    vp
    @7
    cA
    vp
    vs
    weq
    @4
    @8
    vq
    vr
    cX
    cY
    @2
    @7
    @3
    c.le
    breq1
    2rexbidv
    elrab
    syl6bbr
    eqrdv
end
