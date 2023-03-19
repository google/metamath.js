include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnei.mm"
include "cfv.mm"
include "cv.mm"
include "wrex.mm"
include "cpw.mm"
include "crab.mm"
include "neival.mm"
include "eleq2d.mm"
include "wb.mm"
include "wceq.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "topopn.mm"
include "elpw2g.mm"
include "syl.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "adantr.mm"
include "bitrd.mm"

theorem isnei
  let cS: class S
  let vg: setvar g
  let cJ: class J
  let cN: class N
  let cX: class X
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  assume neifval.1: |- X = U. J

  disjoint J g
  disjoint N g
  disjoint S g
  disjoint X g
  disjoint g j
  disjoint g v
  disjoint g x
  disjoint j v
  disjoint j x
  disjoint J j
  disjoint v x
  disjoint J v
  disjoint J x
  disjoint N v
  disjoint P g
  disjoint S v
  disjoint S x
  disjoint X j
  disjoint X v
  disjoint X x
  assert |- ( ( J e. Top /\ S C_ X ) -> ( N e. ( ( nei ` J ) ` S ) <-> ( N C_ X /\ E. g e. J ( S C_ g /\ g C_ N ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    cN
    cS
    vg
    cv
    #
    wss
    #
    @4
    vv
    cv
    #
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    vv
    cX
    cpw
    #
    crab
    #
    wcel
    #
    cN
    cX
    wss
    #
    @5
    @4
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    wa
    #
    @2
    @3
    @11
    cN
    vv
    cS
    vg
    cJ
    cX
    neifval.1
    neival
    eleq2d
    @0
    @12
    @17
    wb
    @1
    @12
    cN
    @10
    wcel
    #
    @16
    wa
    @0
    @17
    @9
    @16
    vv
    cN
    @10
    @6
    cN
    wceq
    #
    @8
    @15
    vg
    cJ
    @19
    @7
    @14
    @5
    @6
    cN
    @4
    sseq2
    anbi2d
    rexbidv
    elrab
    @0
    @18
    @13
    @16
    @0
    cX
    cJ
    wcel
    @18
    @13
    wb
    cJ
    cX
    neifval.1
    topopn
    cN
    cX
    cJ
    elpw2g
    syl
    anbi1d
    syl5bb
    adantr
    bitrd
end
