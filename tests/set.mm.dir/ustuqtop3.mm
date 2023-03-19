include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "wfn.mm"
include "fnresi.mm"
include "fnsnfv.mm"
include "mpan.mm"
include "ad4antlr.mm"
include "simp-4l.mm"
include "simplr.mm"
include "ustdiag.mm"
include "syl2anc.mm"
include "imass1.mm"
include "syl.mm"
include "eqsstrd.mm"
include "fvex.mm"
include "snss.mm"
include "sylibr.mm"
include "fvresi.mm"
include "eqcomd.mm"
include "simpr.mm"
include "3eltr4d.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "ustuqtoplem.mm"
include "mpan2.mm"
include "biimpa.mm"
include "r19.29a.mm"

theorem ustuqtop3
  let vv: setvar v
  let cU: class U
  let cN: class N
  let cX: class X
  let vp: setvar p
  let va: setvar a
  let cA: class A
  let vw: setvar w
  let vq: setvar q
  let cP: class P
  let vb: setvar b
  let vc: setvar c
  let vj: setvar j
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  assume utopustuq.1: |- N = ( p e. X |-> ran ( v e. U |-> ( v " { p } ) ) )

  disjoint p v
  disjoint U p
  disjoint U v
  disjoint X p
  disjoint X v
  disjoint a p
  disjoint N a
  disjoint N p
  disjoint a v
  disjoint U a
  disjoint X a
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
  disjoint a q
  disjoint a r
  disjoint a u
  disjoint a w
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
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j u
  disjoint j w
  disjoint N j
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
  disjoint a x
  disjoint b v
  disjoint b x
  disjoint U b
  disjoint j v
  disjoint j x
  disjoint U j
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
  disjoint X b
  disjoint c v
  disjoint X c
  disjoint X j
  disjoint X r
  disjoint X u
  disjoint X w
  assert |- ( ( ( U e. ( UnifOn ` X ) /\ p e. X ) /\ a e. ( N ` p ) ) -> p e. a )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    vp
    cv
    #
    cX
    wcel
    #
    wa
    #
    va
    cv
    #
    @1
    cN
    cfv
    wcel
    #
    wa
    #
    @4
    vw
    cv
    #
    @1
    csn
    #
    cima
    #
    wceq
    #
    @1
    @4
    wcel
    vw
    cU
    @6
    @7
    cU
    wcel
    #
    wa
    #
    @10
    wa
    #
    @1
    cid
    cX
    cres
    #
    cfv
    #
    @9
    @1
    @4
    @13
    @15
    csn
    #
    @9
    wss
    @15
    @9
    wcel
    @13
    @16
    @14
    @8
    cima
    #
    @9
    @2
    @16
    @17
    wceq
    #
    @0
    @5
    @11
    @10
    @14
    cX
    wfn
    @2
    @18
    cX
    fnresi
    cX
    @1
    @14
    fnsnfv
    mpan
    ad4antlr
    @13
    @14
    @7
    wss
    #
    @17
    @9
    wss
    @13
    @0
    @11
    @19
    @0
    @2
    @5
    @11
    @10
    simp-4l
    @6
    @11
    @10
    simplr
    cU
    @7
    cX
    ustdiag
    syl2anc
    @14
    @7
    @8
    imass1
    syl
    eqsstrd
    @15
    @9
    @1
    @14
    fvex
    snss
    sylibr
    @2
    @1
    @15
    wceq
    @0
    @5
    @11
    @10
    @2
    @15
    @1
    cX
    @1
    fvresi
    eqcomd
    ad4antlr
    @12
    @10
    simpr
    3eltr4d
    @3
    @5
    @10
    vw
    cU
    wrex
    #
    @3
    @4
    cvv
    wcel
    @5
    @20
    wb
    va
    vex
    vw
    vv
    @4
    @1
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    mpan2
    biimpa
    r19.29a
end
