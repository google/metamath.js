include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cfi.mm"
include "wceq.mm"
include "wss.mm"
include "cin.mm"
include "wral.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "simp-6l.mm"
include "simp-7l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "ustincl.mm"
include "syl3anc.mm"
include "simpllr.mm"
include "ineq12.mm"
include "cvv.mm"
include "vex.mm"
include "inimasn.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "sylancom.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "inex1.mm"
include "ustuqtoplem.mm"
include "mpan2.mm"
include "biimpar.mm"
include "simp-4l.mm"
include "biimpa.mm"
include "r19.29a.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "fvex.mm"
include "inficl.mm"
include "sylib.mm"
include "eqimss.mm"
include "syl.mm"

theorem ustuqtop2
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
  assert |- ( ( U e. ( UnifOn ` X ) /\ p e. X ) -> ( fi ` ( N ` p ) ) C_ ( N ` p ) )

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
    @1
    cN
    cfv
    #
    cfi
    cfv
    #
    @4
    wceq
    #
    @5
    @4
    wss
    @3
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    @4
    wcel
    #
    vb
    @4
    wral
    #
    va
    @4
    wral
    #
    @6
    @3
    @11
    va
    @4
    @3
    @7
    @4
    wcel
    #
    wa
    #
    @10
    vb
    @4
    @14
    @8
    @4
    wcel
    #
    wa
    #
    @7
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
    @10
    vw
    cU
    @16
    @17
    cU
    wcel
    #
    wa
    #
    @20
    wa
    #
    @8
    vu
    cv
    #
    @18
    cima
    #
    wceq
    #
    @10
    vu
    cU
    @23
    @24
    cU
    wcel
    #
    wa
    #
    @26
    wa
    #
    @3
    @9
    vx
    cv
    #
    @18
    cima
    #
    wceq
    #
    vx
    cU
    wrex
    #
    @10
    @3
    @13
    @15
    @21
    @20
    @27
    @26
    simp-6l
    @29
    @17
    @24
    cin
    #
    cU
    wcel
    #
    @9
    @34
    @18
    cima
    #
    wceq
    #
    @33
    @29
    @0
    @21
    @27
    @35
    @0
    @2
    @13
    @15
    @21
    @20
    @27
    @26
    simp-7l
    @16
    @21
    @20
    @27
    @26
    simp-4r
    @23
    @27
    @26
    simplr
    cU
    @17
    @24
    cX
    ustincl
    syl3anc
    @28
    @26
    @20
    @37
    @22
    @20
    @27
    @26
    simpllr
    @20
    @26
    wa
    @9
    @19
    @25
    cin
    #
    @36
    @7
    @19
    @8
    @25
    ineq12
    @1
    cvv
    wcel
    @36
    @38
    wceq
    vp
    vex
    @17
    @24
    @1
    cvv
    inimasn
    ax-mp
    syl6eqr
    sylancom
    @32
    @37
    vx
    @34
    cU
    @30
    @34
    wceq
    @31
    @36
    @9
    @30
    @34
    @18
    imaeq1
    eqeq2d
    rspcev
    syl2anc
    @3
    @10
    @33
    @3
    @9
    cvv
    wcel
    @10
    @33
    wb
    @7
    @8
    va
    vex
    #
    inex1
    vx
    vv
    @9
    @1
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    mpan2
    biimpar
    syl2anc
    @23
    @3
    @15
    @26
    vu
    cU
    wrex
    #
    @3
    @13
    @15
    @21
    @20
    simp-4l
    @14
    @15
    @21
    @20
    simpllr
    @3
    @15
    @40
    @3
    @8
    cvv
    wcel
    @15
    @40
    wb
    vb
    vex
    vu
    vv
    @8
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
    syl2anc
    r19.29a
    @14
    @20
    vw
    cU
    wrex
    #
    @15
    @3
    @13
    @41
    @3
    @7
    cvv
    wcel
    @13
    @41
    wb
    @39
    vw
    vv
    @7
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
    adantr
    r19.29a
    ralrimiva
    ralrimiva
    @4
    cvv
    wcel
    @12
    @6
    wb
    @1
    cN
    fvex
    va
    vb
    @4
    cvv
    inficl
    ax-mp
    sylib
    @5
    @4
    eqimss
    syl
end
