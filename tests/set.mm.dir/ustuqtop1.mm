include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wrex.mm"
include "cxp.mm"
include "cun.mm"
include "simpl1l.mm"
include "3anassrs.mm"
include "simplr.mm"
include "ustssxp.mm"
include "syl2anc.mm"
include "simpl1r.mm"
include "snssd.mm"
include "simpl3.mm"
include "xpss12.mm"
include "unssd.mm"
include "ssun1.mm"
include "a1i.mm"
include "ustssel.mm"
include "imp.mm"
include "syl31anc.mm"
include "simpl2.mm"
include "ssequn1.mm"
include "biimpi.mm"
include "id.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "inidm.mm"
include "vex.mm"
include "snnz.mm"
include "eqnetri.mm"
include "xpima2.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "uneq12d.mm"
include "imaundir.mm"
include "syl6eqr.mm"
include "sylan9req.mm"
include "sylancom.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "cvv.mm"
include "wb.mm"
include "ustuqtoplem.mm"
include "mpan2.mm"
include "biimpa.mm"
include "3ad2antl1.mm"
include "r19.29a.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "mpbird.mm"

theorem ustuqtop1
  let vv: setvar v
  let cU: class U
  let cN: class N
  let cX: class X
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cA: class A
  let vw: setvar w
  let vq: setvar q
  let cP: class P
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
  disjoint a b
  disjoint a p
  disjoint N a
  disjoint b p
  disjoint N b
  disjoint N p
  disjoint a v
  disjoint U a
  disjoint b v
  disjoint U b
  disjoint X a
  disjoint X b
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
  disjoint a c
  disjoint a j
  disjoint a q
  disjoint a r
  disjoint a u
  disjoint a w
  disjoint b c
  disjoint b j
  disjoint b q
  disjoint b r
  disjoint b u
  disjoint b w
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
  disjoint b x
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
  disjoint c v
  disjoint X c
  disjoint X j
  disjoint X r
  disjoint X u
  disjoint X w
  assert |- ( ( ( ( U e. ( UnifOn ` X ) /\ p e. X ) /\ a C_ b /\ b C_ X ) /\ a e. ( N ` p ) ) -> b e. ( N ` p ) )

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
    vb
    cv
    #
    wss
    #
    @5
    cX
    wss
    #
    w3a
    #
    @4
    @1
    cN
    cfv
    #
    wcel
    #
    wa
    #
    @5
    @9
    wcel
    #
    @5
    vu
    cv
    #
    @1
    csn
    #
    cima
    #
    wceq
    #
    vu
    cU
    wrex
    #
    @11
    @4
    vw
    cv
    #
    @14
    cima
    #
    wceq
    #
    @17
    vw
    cU
    @11
    @18
    cU
    wcel
    #
    wa
    #
    @20
    wa
    #
    @18
    @14
    @5
    cxp
    #
    cun
    #
    cU
    wcel
    #
    @5
    @25
    @14
    cima
    #
    wceq
    #
    @17
    @23
    @0
    @21
    @25
    cX
    cX
    cxp
    #
    wss
    #
    @18
    @25
    wss
    #
    @26
    @8
    @10
    @21
    @20
    @0
    @0
    @2
    @6
    @7
    @10
    @21
    @20
    w3a
    #
    simpl1l
    3anassrs
    #
    @11
    @21
    @20
    simplr
    #
    @23
    @18
    @24
    @29
    @23
    @0
    @21
    @18
    @29
    wss
    @33
    @34
    cU
    @18
    cX
    ustssxp
    syl2anc
    @23
    @14
    cX
    wss
    @7
    @24
    @29
    wss
    @23
    @1
    cX
    @8
    @10
    @21
    @20
    @2
    @0
    @2
    @6
    @7
    @32
    simpl1r
    3anassrs
    snssd
    @8
    @10
    @21
    @20
    @7
    @3
    @6
    @7
    @32
    simpl3
    3anassrs
    @14
    cX
    @5
    cX
    xpss12
    syl2anc
    unssd
    @31
    @23
    @18
    @24
    ssun1
    a1i
    @0
    @21
    @30
    w3a
    @31
    @26
    cU
    @18
    @25
    cX
    ustssel
    imp
    syl31anc
    @22
    @20
    @6
    @28
    @8
    @10
    @21
    @20
    @6
    @3
    @6
    @7
    @32
    simpl2
    3anassrs
    @6
    @20
    @5
    @4
    @5
    cun
    #
    @27
    @6
    @35
    @5
    wceq
    @4
    @5
    ssequn1
    biimpi
    @20
    @35
    @19
    @24
    @14
    cima
    #
    cun
    @27
    @20
    @4
    @19
    @5
    @36
    @20
    id
    @20
    @36
    @5
    @14
    @14
    cin
    #
    c0
    wne
    @36
    @5
    wceq
    @20
    @37
    @14
    c0
    @14
    inidm
    @1
    vp
    vex
    snnz
    eqnetri
    @14
    @5
    @14
    xpima2
    mp1i
    eqcomd
    uneq12d
    @18
    @24
    @14
    imaundir
    syl6eqr
    sylan9req
    sylancom
    @16
    @28
    vu
    @25
    cU
    @13
    @25
    wceq
    @15
    @27
    @5
    @13
    @25
    @14
    imaeq1
    eqeq2d
    rspcev
    syl2anc
    @3
    @6
    @10
    @20
    vw
    cU
    wrex
    #
    @7
    @3
    @10
    @38
    @3
    @4
    cvv
    wcel
    @10
    @38
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
    3ad2antl1
    r19.29a
    @8
    @12
    @17
    wb
    #
    @10
    @3
    @6
    @39
    @7
    @3
    @5
    cvv
    wcel
    @39
    vb
    vex
    vu
    vv
    @5
    @1
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    mpan2
    3ad2ant1
    adantr
    mpbird
end
