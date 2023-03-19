include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfbas.mm"
include "cpw.mm"
include "wss.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "wceq.mm"
include "crp.mm"
include "metustel.mm"
include "simpr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cxr.mm"
include "wf.mm"
include "psmetf.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "ex.mm"
include "rexlimdvw.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "pwssb.mm"
include "sylibr.mm"
include "adantl.mm"
include "wex.mm"
include "cvv.mm"
include "c1.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "elisset.mm"
include "1rp.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan.mm"
include "eximi.mm"
include "4syl.mm"
include "exbidv.mm"
include "mpbird.mm"
include "n0.mm"
include "wn.mm"
include "cid.mm"
include "cres.mm"
include "metustid.mm"
include "adantll.mm"
include "biimpi.mm"
include "cop.mm"
include "opelresi.mm"
include "ibir.mm"
include "ne0i.mm"
include "exlimiv.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "nelrdva.mm"
include "df-nel.mm"
include "df-ss.mm"
include "simplrl.mm"
include "eqeltrd.mm"
include "sseqin2.mm"
include "simplrr.mm"
include "wo.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "metustto.mm"
include "syl3anc.mm"
include "mpjaodan.mm"
include "vex.mm"
include "inex1.mm"
include "pwid.mm"
include "a1i.mm"
include "elpwid.mm"
include "sseq1.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "wb.mm"
include "elfvex.mm"
include "xpexg.mm"
include "isfbas2.mm"
include "mpbir2and.mm"

theorem metustfbas
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let cA: class A
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let vv: setvar v
  let vu: setvar u
  let vw: setvar w
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint F a
  disjoint B a
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  disjoint a p
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint a x
  disjoint p x
  disjoint D p
  disjoint q x
  disjoint D q
  disjoint D x
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X p
  disjoint X q
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a r
  disjoint a v
  disjoint p r
  disjoint p v
  disjoint q r
  disjoint q v
  disjoint r v
  disjoint A r
  disjoint A v
  disjoint a u
  disjoint a w
  disjoint r u
  disjoint r w
  disjoint D r
  disjoint u v
  disjoint u w
  disjoint D u
  disjoint v w
  disjoint D v
  disjoint D w
  disjoint F r
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint X r
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint a y
  disjoint D y
  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> F e. ( fBas ` ( X X. X ) ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    wa
    #
    cF
    cX
    cX
    cxp
    #
    cfbas
    cfv
    wcel
    #
    cF
    @4
    cpw
    wss
    #
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    #
    vz
    cF
    wrex
    #
    vy
    cF
    wral
    vx
    cF
    wral
    #
    w3a
    #
    @2
    @6
    @0
    @2
    @10
    @4
    wss
    #
    vx
    cF
    wral
    @6
    @2
    @17
    vx
    cF
    @2
    @10
    cF
    wcel
    #
    @10
    cD
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    va
    crp
    wrex
    #
    @17
    @10
    cD
    cF
    cX
    va
    metust.1
    metustel
    #
    @2
    @23
    @17
    va
    crp
    @2
    @23
    @17
    @2
    @23
    wa
    #
    @10
    @22
    @4
    @2
    @23
    simpr
    @26
    cD
    cdm
    #
    @22
    @4
    cD
    @21
    cnvimass
    @2
    @27
    @4
    wceq
    #
    @23
    @2
    @4
    cxr
    cD
    wf
    @28
    cD
    cX
    psmetf
    @4
    cxr
    cD
    fdm
    syl
    adantr
    syl5sseq
    eqsstrd
    ex
    rexlimdvw
    sylbid
    ralrimiv
    vx
    cF
    @4
    pwssb
    sylibr
    adantl
    @3
    @7
    @8
    @15
    @3
    @18
    vx
    wex
    #
    @7
    @2
    @29
    @0
    @2
    @29
    @24
    vx
    wex
    #
    @2
    @19
    cvv
    wcel
    @19
    cc0
    c1
    cico
    co
    #
    cima
    #
    cvv
    wcel
    @10
    @32
    wceq
    #
    vx
    wex
    @30
    cD
    @1
    cnvexg
    @19
    @31
    cvv
    imaexg
    vx
    @32
    cvv
    elisset
    @33
    @24
    vx
    c1
    crp
    wcel
    @33
    @24
    1rp
    @23
    @33
    va
    c1
    crp
    @20
    c1
    wceq
    #
    @22
    @32
    @10
    @34
    @21
    @31
    @19
    @20
    c1
    cc0
    cico
    oveq2
    imaeq2d
    eqeq2d
    rspcev
    mpan
    eximi
    4syl
    @2
    @18
    @24
    vx
    @25
    exbidv
    mpbird
    adantl
    vx
    cF
    n0
    sylibr
    @3
    c0
    cF
    wcel
    wn
    @8
    @3
    vx
    cF
    c0
    @3
    @18
    wa
    cid
    cX
    cres
    #
    @10
    wss
    #
    @35
    c0
    wne
    #
    @10
    c0
    wne
    @2
    @18
    @36
    @0
    @10
    cD
    cF
    cX
    va
    metust.1
    metustid
    adantll
    @3
    @37
    @18
    @3
    vp
    cv
    #
    cX
    wcel
    #
    vp
    wex
    #
    @37
    @0
    @40
    @2
    @0
    @40
    vp
    cX
    n0
    biimpi
    adantr
    @39
    @37
    vp
    @39
    @38
    @38
    cop
    #
    @35
    wcel
    #
    @37
    @39
    @42
    @38
    cX
    cX
    opelresi
    ibir
    @35
    @41
    ne0i
    syl
    exlimiv
    syl
    adantr
    @35
    @10
    ssn0
    syl2anc
    nelrdva
    c0
    cF
    df-nel
    sylibr
    @3
    @14
    vx
    vy
    cF
    cF
    @3
    @18
    @11
    cF
    wcel
    #
    wa
    #
    wa
    #
    @12
    cF
    wcel
    #
    @12
    @12
    wss
    #
    @14
    @45
    @10
    @11
    wss
    #
    @46
    @11
    @10
    wss
    #
    @45
    @48
    wa
    @12
    @10
    cF
    @48
    @12
    @10
    wceq
    #
    @45
    @48
    @50
    @10
    @11
    df-ss
    biimpi
    adantl
    @3
    @18
    @43
    @48
    simplrl
    eqeltrd
    @45
    @49
    wa
    @12
    @11
    cF
    @49
    @12
    @11
    wceq
    #
    @45
    @49
    @51
    @11
    @10
    sseqin2
    biimpi
    adantl
    @3
    @18
    @43
    @49
    simplrr
    eqeltrd
    @45
    @2
    @18
    @43
    @48
    @49
    wo
    @0
    @2
    @44
    simplr
    @3
    @18
    @43
    simprl
    @3
    @18
    @43
    simprr
    @10
    @11
    cD
    cF
    cX
    va
    metust.1
    metustto
    syl3anc
    mpjaodan
    @45
    @12
    @12
    @12
    @12
    cpw
    wcel
    @45
    @12
    @10
    @11
    vx
    vex
    inex1
    pwid
    a1i
    elpwid
    @13
    @47
    vz
    @12
    cF
    @9
    @12
    @12
    sseq1
    rspcev
    syl2anc
    ralrimivva
    3jca
    @3
    @4
    cvv
    wcel
    #
    @5
    @6
    @16
    wa
    wb
    @3
    cX
    cvv
    wcel
    #
    @53
    @52
    @2
    @53
    @0
    cD
    cX
    cpsmet
    elfvex
    adantl
    #
    @54
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    vx
    vy
    vz
    cvv
    @4
    cF
    isfbas2
    syl
    mpbir2and
end
