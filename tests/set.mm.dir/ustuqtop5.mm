include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wrex.mm"
include "cxp.mm"
include "ustbasel.mm"
include "adantr.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "snssi.mm"
include "dfss.mm"
include "sylib.mm"
include "incom.mm"
include "syl6req.mm"
include "snnzg.mm"
include "eqnetrd.mm"
include "adantl.mm"
include "xpima2.mm"
include "syl.mm"
include "eqcomd.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "ustuqtoplem.mm"
include "mpidan.mm"
include "mpbird.mm"

theorem ustuqtop5
  let vv: setvar v
  let cU: class U
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
  disjoint N p
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
  disjoint a v
  disjoint a x
  disjoint U a
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
  disjoint X a
  disjoint X b
  disjoint c v
  disjoint X c
  disjoint X j
  disjoint X r
  disjoint X u
  disjoint X w
  assert |- ( ( U e. ( UnifOn ` X ) /\ p e. X ) -> X e. ( N ` p ) )

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
    cX
    @1
    cN
    cfv
    wcel
    #
    cX
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
    vw
    cU
    wrex
    #
    @3
    cX
    cX
    cxp
    #
    cU
    wcel
    #
    cX
    @10
    @6
    cima
    #
    wceq
    #
    @9
    @0
    @11
    @2
    cU
    cX
    ustbasel
    adantr
    @3
    @12
    cX
    @3
    cX
    @6
    cin
    #
    c0
    wne
    #
    @12
    cX
    wceq
    @2
    @15
    @0
    @2
    @14
    @6
    c0
    @2
    @6
    @6
    cX
    cin
    #
    @14
    @2
    @6
    cX
    wss
    @6
    @16
    wceq
    @1
    cX
    snssi
    @6
    cX
    dfss
    sylib
    @6
    cX
    incom
    syl6req
    @1
    cX
    snnzg
    eqnetrd
    adantl
    cX
    cX
    @6
    xpima2
    syl
    eqcomd
    @8
    @13
    vw
    @10
    cU
    @5
    @10
    wceq
    @7
    @12
    cX
    @5
    @10
    @6
    imaeq1
    eqeq2d
    rspcev
    syl2anc
    @0
    @2
    cX
    cvv
    wcel
    @4
    @9
    wb
    cU
    cX
    cust
    elfvex
    vw
    vv
    cX
    @1
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    mpidan
    mpbird
end
