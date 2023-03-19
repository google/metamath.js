include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "ctg.mm"
include "cfv.mm"
include "ciin.mm"
include "cin.mm"
include "cfne.mm"
include "wbr.mm"
include "c0.mm"
include "wi.mm"
include "riin0.mm"
include "unieqd.mm"
include "unipw.mm"
include "syl6req.mm"
include "a1i.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "w3a.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspccva.mm"
include "3adant1.mm"
include "fnemeet1.mm"
include "eqid.mm"
include "fnebas.mm"
include "syl.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "adantr.mm"
include "adantl.mm"
include "ex.mm"
include "fnetr.mm"
include "expcom.mm"
include "3expa.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "wss.mm"
include "simprl.mm"
include "eqtr3d.mm"
include "eqimss2.mm"
include "ad2antrl.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "breq2.mm"
include "cbvralv.mm"
include "fnetg.mm"
include "ralimi.mm"
include "sylbi.mm"
include "ad2antll.mm"
include "ssiin.mm"
include "ssind.mm"
include "cvv.mm"
include "pwexg.mm"
include "inex1g.mm"
include "ad2antrr.mm"
include "bastg.mm"
include "sstrd.mm"
include "isfne4.mm"
include "sylanbrc.mm"
include "impbid.mm"

theorem fnemeet2
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cS: class S
  let cT: class T
  let cV: class V
  let cX: class X
  let cA: class A
  let vj: setvar j
  let vk: setvar k

  disjoint t y
  disjoint t x
  disjoint S t
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint V t
  disjoint V x
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint T t
  disjoint T x
  disjoint A t
  disjoint A y
  disjoint j k
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint S j
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint S k
  disjoint V j
  disjoint V k
  disjoint X j
  disjoint X k
  assert |- ( ( X e. V /\ A. y e. S X = U. y ) -> ( T Fne ( ~P X i^i |^|_ t e. S ( topGen ` t ) ) <-> ( X = U. T /\ A. x e. S T Fne x ) ) )

  proof
    cX
    cV
    wcel
    #
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vy
    cS
    wral
    #
    wa
    #
    cT
    cX
    cpw
    #
    vt
    cS
    vt
    cv
    #
    ctg
    cfv
    #
    ciin
    #
    cin
    #
    cfne
    wbr
    #
    cX
    cT
    cuni
    #
    wceq
    #
    cT
    vx
    cv
    #
    cfne
    wbr
    #
    vx
    cS
    wral
    #
    wa
    #
    @5
    @11
    @13
    @16
    @5
    @11
    @13
    @5
    @11
    wa
    cX
    @10
    cuni
    #
    @12
    @5
    cX
    @18
    wceq
    #
    @11
    @5
    @19
    cS
    c0
    cS
    c0
    wceq
    #
    @19
    wi
    @5
    @20
    @18
    @6
    cuni
    cX
    @20
    @10
    @6
    vt
    @6
    @8
    cS
    riin0
    unieqd
    cX
    unipw
    syl6req
    a1i
    cS
    c0
    wne
    @14
    cS
    wcel
    #
    vx
    wex
    @5
    @19
    vx
    cS
    n0
    @5
    @21
    @19
    vx
    @0
    @4
    @21
    @19
    @0
    @4
    @21
    w3a
    #
    cX
    @14
    cuni
    #
    @18
    @4
    @21
    cX
    @23
    wceq
    #
    @0
    @3
    @24
    vy
    @14
    cS
    @1
    @14
    wceq
    @2
    @23
    cX
    @1
    @14
    unieq
    eqeq2d
    rspccva
    3adant1
    @22
    @10
    @14
    cfne
    wbr
    #
    @18
    @23
    wceq
    vy
    vt
    @14
    cS
    cV
    cX
    fnemeet1
    #
    @10
    @14
    @18
    @23
    @18
    eqid
    #
    @23
    eqid
    fnebas
    syl
    eqtr4d
    3expia
    exlimdv
    syl5bi
    pm2.61dne
    #
    adantr
    @11
    @12
    @18
    wceq
    #
    @5
    cT
    @10
    @12
    @18
    @12
    eqid
    #
    @27
    fnebas
    adantl
    eqtr4d
    ex
    @5
    @11
    @15
    vx
    cS
    @0
    @4
    @21
    @11
    @15
    wi
    #
    @22
    @25
    @31
    @26
    @11
    @25
    @15
    cT
    @10
    @14
    fnetr
    expcom
    syl
    3expa
    ralrimdva
    jcad
    @5
    @17
    @11
    @5
    @17
    wa
    #
    @29
    cT
    @10
    ctg
    cfv
    #
    wss
    @11
    @32
    cX
    @12
    @18
    @5
    @13
    @16
    simprl
    @5
    @19
    @17
    @28
    adantr
    eqtr3d
    @32
    cT
    @10
    @33
    @32
    cT
    @6
    @9
    @32
    @12
    cX
    wss
    #
    cT
    @6
    wss
    @13
    @34
    @5
    @16
    @12
    cX
    eqimss2
    ad2antrl
    cT
    cX
    sspwuni
    sylibr
    @32
    cT
    @8
    wss
    #
    vt
    cS
    wral
    #
    cT
    @9
    wss
    @16
    @36
    @5
    @13
    @16
    cT
    @7
    cfne
    wbr
    #
    vt
    cS
    wral
    @36
    @15
    @37
    vx
    vt
    cS
    @14
    @7
    cT
    cfne
    breq2
    cbvralv
    @37
    @35
    vt
    cS
    cT
    @7
    fnetg
    ralimi
    sylbi
    ad2antll
    vt
    cS
    @8
    cT
    ssiin
    sylibr
    ssind
    @32
    @10
    cvv
    wcel
    #
    @10
    @33
    wss
    @0
    @38
    @4
    @17
    @0
    @6
    cvv
    wcel
    @38
    cX
    cV
    pwexg
    @6
    @9
    cvv
    inex1g
    syl
    ad2antrr
    @10
    cvv
    bastg
    syl
    sstrd
    cT
    @10
    @12
    @18
    @30
    @27
    isfne4
    sylanbrc
    ex
    impbid
end
