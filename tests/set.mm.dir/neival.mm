include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "neifval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "wb.mm"
include "topopn.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem neival
  let vv: setvar v
  let cS: class S
  let vg: setvar g
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  let cN: class N
  let cP: class P
  assume neifval.1: |- X = U. J

  disjoint g v
  disjoint J g
  disjoint J v
  disjoint S g
  disjoint S v
  disjoint X g
  disjoint X v
  disjoint g j
  disjoint g x
  disjoint j v
  disjoint j x
  disjoint J j
  disjoint v x
  disjoint J x
  disjoint N g
  disjoint N v
  disjoint P g
  disjoint S x
  disjoint X j
  disjoint X x
  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( nei ` J ) ` S ) = { v e. ~P X | E. g e. J ( S C_ g /\ g C_ v ) } )

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
    cS
    cJ
    cnei
    cfv
    #
    cfv
    #
    cS
    vx
    cX
    cpw
    #
    vx
    cv
    #
    vg
    cv
    #
    wss
    #
    @7
    vv
    cv
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    vv
    @5
    crab
    #
    cmpt
    #
    cfv
    #
    cS
    @7
    wss
    #
    @9
    wa
    #
    vg
    cJ
    wrex
    #
    vv
    @5
    crab
    #
    @0
    @4
    @14
    wceq
    @1
    @0
    cS
    @3
    @13
    vx
    vv
    vg
    cJ
    cX
    neifval.1
    neifval
    fveq1d
    adantr
    @2
    cS
    @5
    wcel
    #
    @18
    cvv
    wcel
    #
    @14
    @18
    wceq
    @0
    @19
    @1
    @0
    cX
    cJ
    wcel
    #
    @19
    @1
    wb
    cJ
    cX
    neifval.1
    topopn
    #
    cS
    cX
    cJ
    elpw2g
    syl
    biimpar
    @0
    @20
    @1
    @0
    @21
    @5
    cvv
    wcel
    @20
    @22
    cX
    cJ
    pwexg
    @17
    vv
    @5
    cvv
    rabexg
    3syl
    adantr
    vx
    cS
    @12
    @18
    @5
    cvv
    @13
    @6
    cS
    wceq
    #
    @11
    @17
    vv
    @5
    @23
    @10
    @16
    vg
    cJ
    @23
    @8
    @15
    @9
    @6
    cS
    @7
    sseq1
    anbi1d
    rexbidv
    rabbidv
    @13
    eqid
    fvmptg
    syl2anc
    eqtrd
end
