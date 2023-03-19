include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cmpt.mm"
include "wceq.mm"
include "ctopon.mm"
include "wreu.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cbvralv.mm"
include "eleq1.mm"
include "raleqbi1dv.mm"
include "syl5bbr.mm"
include "cbvrabv.mm"
include "ustuqtop0.mm"
include "ustuqtop1.mm"
include "ustuqtop2.mm"
include "ustuqtop3.mm"
include "ustuqtop4.mm"
include "ustuqtop5.mm"
include "neiptopreu.mm"
include "feqmptd.mm"
include "eqeq1d.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "reubidv.mm"
include "mpbid.mm"

theorem ustuqtop
  let vv: setvar v
  let cU: class U
  let vj: setvar j
  let cN: class N
  let cX: class X
  let vp: setvar p
  let cA: class A
  let vw: setvar w
  let vq: setvar q
  let cP: class P
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  assume utopustuq.1: |- N = ( p e. X |-> ran ( v e. U |-> ( v " { p } ) ) )

  disjoint p v
  disjoint U p
  disjoint U v
  disjoint X p
  disjoint X v
  disjoint j p
  disjoint N j
  disjoint N p
  disjoint j v
  disjoint U j
  disjoint X j
  disjoint A w
  disjoint q v
  disjoint q w
  disjoint P q
  disjoint v w
  disjoint P v
  disjoint P w
  disjoint p q
  disjoint p w
  disjoint U q
  disjoint U w
  disjoint X q
  disjoint a b
  disjoint a c
  disjoint a j
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a u
  disjoint a w
  disjoint N a
  disjoint b c
  disjoint b j
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b u
  disjoint b w
  disjoint N b
  disjoint c j
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c u
  disjoint c w
  disjoint N c
  disjoint j q
  disjoint j r
  disjoint j u
  disjoint j w
  disjoint p r
  disjoint p u
  disjoint q r
  disjoint q u
  disjoint N q
  disjoint r u
  disjoint r w
  disjoint N r
  disjoint u w
  disjoint N u
  disjoint N w
  disjoint a v
  disjoint a x
  disjoint U a
  disjoint b v
  disjoint b x
  disjoint U b
  disjoint j x
  disjoint p x
  disjoint q x
  disjoint r v
  disjoint r x
  disjoint U r
  disjoint u v
  disjoint u x
  disjoint U u
  disjoint v x
  disjoint w x
  disjoint U x
  disjoint X a
  disjoint X b
  disjoint c v
  disjoint X c
  disjoint X r
  disjoint X u
  disjoint X w
  disjoint N x
  disjoint X x
  assert |- ( U e. ( UnifOn ` X ) -> E! j e. ( TopOn ` X ) A. p e. X ( N ` p ) = ( ( nei ` j ) ` { p } ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cN
    vp
    cX
    vp
    cv
    #
    csn
    vj
    cv
    cnei
    cfv
    cfv
    #
    cmpt
    #
    wceq
    #
    vj
    cX
    ctopon
    cfv
    #
    wreu
    @1
    cN
    cfv
    #
    @2
    wceq
    vp
    cX
    wral
    #
    vj
    @5
    wreu
    @0
    vj
    vc
    cv
    #
    vr
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vr
    @8
    wral
    #
    vc
    cX
    cpw
    #
    crab
    cN
    cX
    vx
    vp
    va
    vb
    @12
    va
    cv
    #
    @6
    wcel
    #
    vp
    @14
    wral
    #
    vc
    va
    @13
    @12
    @8
    @6
    wcel
    #
    vp
    @8
    wral
    @8
    @14
    wceq
    @16
    @17
    @11
    vp
    vr
    @8
    @1
    @9
    wceq
    @6
    @10
    @8
    @1
    @9
    cN
    fveq2
    eleq2d
    cbvralv
    @17
    @15
    vp
    @8
    @14
    @8
    @14
    @6
    eleq1
    raleqbi1dv
    syl5bbr
    cbvrabv
    vv
    cU
    cN
    cX
    vp
    utopustuq.1
    ustuqtop0
    #
    vv
    cU
    cN
    cX
    vp
    va
    vb
    utopustuq.1
    ustuqtop1
    vv
    cU
    cN
    cX
    vp
    utopustuq.1
    ustuqtop2
    vv
    cU
    cN
    cX
    vp
    va
    utopustuq.1
    ustuqtop3
    vv
    cU
    cN
    cX
    vx
    vp
    va
    vb
    utopustuq.1
    ustuqtop4
    vv
    cU
    cN
    cX
    vp
    utopustuq.1
    ustuqtop5
    neiptopreu
    @0
    @4
    @7
    vj
    @5
    @0
    @4
    vp
    cX
    @6
    cmpt
    #
    @3
    wceq
    #
    @7
    @0
    cN
    @19
    @3
    @0
    vp
    cX
    @13
    cpw
    cN
    @18
    feqmptd
    eqeq1d
    @6
    cvv
    wcel
    #
    vp
    cX
    wral
    @20
    @7
    wb
    @21
    vp
    cX
    @1
    cN
    fvex
    rgenw
    vp
    cX
    @6
    @2
    cvv
    mpteqb
    ax-mp
    syl6bb
    reubidv
    mpbid
end
