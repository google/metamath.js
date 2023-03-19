include "wcel.mm"
include "cwunm.mm"
include "cfv.mm"
include "cwun.mm"
include "wss.mm"
include "wa.mm"
include "wunex2.mm"
include "wuncss.mm"
include "syl.mm"
include "com.mm"
include "cv.mm"
include "ciun.mm"
include "crn.mm"
include "cuni.mm"
include "wfn.mm"
include "wceq.mm"
include "cvv.mm"
include "cun.mm"
include "cpw.mm"
include "cpr.mm"
include "cmpt.mm"
include "c1o.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fniunfv.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "wral.mm"
include "c0.mm"
include "csuc.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "weq.mm"
include "con0.mm"
include "1on.mm"
include "unexg.mm"
include "mpan2.mm"
include "fveq1i.mm"
include "fr0g.mm"
include "syl5eq.mm"
include "wuncid.mm"
include "csn.mm"
include "df1o2.mm"
include "wunccl.mm"
include "wun0.mm"
include "snssd.mm"
include "syl5eqss.mm"
include "unssd.mm"
include "eqsstrd.mm"
include "wi.mm"
include "simplr.mm"
include "fvex.mm"
include "uniex.mm"
include "unex.mm"
include "prex.mm"
include "mptex.mm"
include "rnex.mm"
include "iunex.mm"
include "id.mm"
include "unieq.mm"
include "uneq12d.mm"
include "pweq.mm"
include "preq12d.mm"
include "preq1.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "cbviunv.mm"
include "preq2.mm"
include "cbvmptv.mm"
include "mpteq1.mm"
include "uneq2d.mm"
include "iuneq12d.mm"
include "frsucmpt2.mm"
include "sylancl.mm"
include "simpr.mm"
include "ad3antrrr.mm"
include "sselda.mm"
include "wunelss.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "sylibr.mm"
include "wunpw.mm"
include "wununi.mm"
include "prssi.mm"
include "syl2anc.mm"
include "wf.mm"
include "adantr.mm"
include "wunpr.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "iunss.mm"
include "ex.mm"
include "expcom.mm"
include "finds2.mm"
include "com12.mm"
include "ralrimiv.mm"
include "eqssd.mm"

theorem wuncval2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cU: class U
  let cF: class F
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vm: setvar m
  let vn: setvar n
  assume wuncval2.f: |- F = ( rec ( ( z e. _V |-> ( ( z u. U. z ) u. U_ x e. z ( { ~P x , U. x } u. ran ( y e. z |-> { x , y } ) ) ) ) , ( A u. 1o ) ) |` _om )
  assume wuncval2.u: |- U = U. ran F

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint V x
  disjoint V y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint U u
  disjoint V m
  disjoint V n
  disjoint V u
  disjoint V v
  disjoint F m
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint F w
  assert |- ( A e. V -> ( wUniCl ` A ) = U )

  proof
    cA
    cV
    wcel
    #
    cA
    cwunm
    cfv
    #
    cU
    @0
    cU
    cwun
    wcel
    cA
    cU
    wss
    wa
    @1
    cU
    wss
    vx
    vy
    vz
    cA
    cU
    cF
    cV
    wuncval2.f
    wuncval2.u
    wunex2
    cA
    cU
    wuncss
    syl
    @0
    cU
    vm
    com
    vm
    cv
    #
    cF
    cfv
    #
    ciun
    #
    @1
    cU
    cF
    crn
    cuni
    #
    @4
    wuncval2.u
    cF
    com
    wfn
    #
    @4
    @5
    wceq
    @6
    vz
    cvv
    vz
    cv
    #
    @7
    cuni
    #
    cun
    #
    vx
    @7
    vx
    cv
    #
    cpw
    #
    @10
    cuni
    #
    cpr
    #
    vy
    @7
    @10
    vy
    cv
    #
    cpr
    #
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cun
    #
    cmpt
    #
    cA
    c1o
    cun
    #
    crdg
    com
    cres
    #
    com
    wfn
    @22
    @21
    frfnom
    com
    cF
    @23
    wuncval2.f
    fneq1i
    mpbir
    vm
    com
    cF
    fniunfv
    ax-mp
    eqtr4i
    @0
    @3
    @1
    wss
    #
    vm
    com
    wral
    @4
    @1
    wss
    @0
    @24
    vm
    com
    @2
    com
    wcel
    @0
    @24
    @24
    c0
    cF
    cfv
    #
    @1
    wss
    vn
    cv
    #
    cF
    cfv
    #
    @1
    wss
    #
    @26
    csuc
    #
    cF
    cfv
    #
    @1
    wss
    #
    @0
    vm
    vn
    @2
    c0
    wceq
    @3
    @25
    @1
    @2
    c0
    cF
    fveq2
    sseq1d
    vm
    vn
    weq
    @3
    @27
    @1
    @2
    @26
    cF
    fveq2
    sseq1d
    @2
    @29
    wceq
    @3
    @30
    @1
    @2
    @29
    cF
    fveq2
    sseq1d
    @0
    @25
    @22
    @1
    @0
    @22
    cvv
    wcel
    #
    @25
    @22
    wceq
    @0
    c1o
    con0
    wcel
    @32
    1on
    cA
    c1o
    cV
    con0
    unexg
    mpan2
    @32
    @25
    c0
    @23
    cfv
    @22
    c0
    cF
    @23
    wuncval2.f
    fveq1i
    @22
    cvv
    @21
    fr0g
    syl5eq
    syl
    @0
    cA
    c1o
    @1
    cA
    cV
    wuncid
    @0
    c1o
    c0
    csn
    @1
    df1o2
    @0
    c0
    @1
    @0
    @1
    cA
    cV
    wunccl
    #
    wun0
    snssd
    syl5eqss
    unssd
    eqsstrd
    @0
    @26
    com
    wcel
    #
    @28
    @31
    wi
    @0
    @34
    wa
    #
    @28
    @31
    @35
    @28
    wa
    #
    @30
    @27
    @27
    cuni
    #
    cun
    #
    vu
    @27
    vu
    cv
    #
    cpw
    #
    @39
    cuni
    #
    cpr
    #
    vv
    @27
    @39
    vv
    cv
    #
    cpr
    #
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cun
    #
    @1
    @36
    @34
    @49
    cvv
    wcel
    @30
    @49
    wceq
    @0
    @34
    @28
    simplr
    @38
    @48
    @27
    @37
    @26
    cF
    fvex
    #
    @27
    @50
    uniex
    unex
    vu
    @27
    @47
    @50
    @42
    @46
    @40
    @41
    prex
    @45
    vv
    @27
    @44
    @50
    mptex
    rnex
    unex
    iunex
    unex
    vz
    vw
    @22
    @26
    @20
    @49
    vw
    cv
    #
    @51
    cuni
    #
    cun
    #
    vu
    @51
    @42
    vv
    @51
    @44
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cun
    cF
    cvv
    wuncval2.f
    vw
    vz
    weq
    #
    @53
    @9
    @57
    @19
    @58
    @51
    @7
    @52
    @8
    @58
    id
    #
    @51
    @7
    unieq
    uneq12d
    @58
    @57
    vx
    @51
    @13
    vv
    @51
    @10
    @43
    cpr
    #
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    @19
    vu
    vx
    @51
    @56
    @63
    vu
    vx
    weq
    #
    @42
    @13
    @55
    @62
    @64
    @40
    @11
    @41
    @12
    @39
    @10
    pweq
    @39
    @10
    unieq
    preq12d
    @64
    @54
    @61
    @64
    vv
    @51
    @44
    @60
    @39
    @10
    @43
    preq1
    mpteq2dv
    rneqd
    uneq12d
    cbviunv
    @58
    vx
    @51
    @7
    @63
    @18
    @59
    @58
    @62
    @17
    @13
    @58
    @61
    @16
    @58
    @61
    vy
    @51
    @15
    cmpt
    @16
    vv
    vy
    @51
    @60
    @15
    @43
    @14
    @10
    preq2
    cbvmptv
    vy
    @51
    @7
    @15
    mpteq1
    syl5eq
    rneqd
    uneq2d
    iuneq12d
    syl5eq
    uneq12d
    @51
    @27
    wceq
    #
    @53
    @38
    @57
    @48
    @65
    @51
    @27
    @52
    @37
    @65
    id
    #
    @51
    @27
    unieq
    uneq12d
    @65
    vu
    @51
    @27
    @56
    @47
    @66
    @65
    @55
    @46
    @42
    @65
    @54
    @45
    vv
    @51
    @27
    @44
    mpteq1
    rneqd
    uneq2d
    iuneq12d
    uneq12d
    frsucmpt2
    sylancl
    @36
    @38
    @48
    @1
    @36
    @27
    @37
    @1
    @35
    @28
    simpr
    #
    @36
    @39
    @1
    wss
    #
    vu
    @27
    wral
    @37
    @1
    wss
    @36
    @68
    vu
    @27
    @36
    @39
    @27
    wcel
    #
    wa
    #
    @39
    @1
    @0
    @1
    cwun
    wcel
    #
    @34
    @28
    @69
    @33
    ad3antrrr
    #
    @36
    @27
    @1
    @39
    @67
    sselda
    #
    wunelss
    ralrimiva
    vu
    @27
    @1
    unissb
    sylibr
    unssd
    @36
    @47
    @1
    wss
    #
    vu
    @27
    wral
    @48
    @1
    wss
    @36
    @74
    vu
    @27
    @70
    @42
    @46
    @1
    @70
    @40
    @1
    wcel
    @41
    @1
    wcel
    @42
    @1
    wss
    @70
    @39
    @1
    @72
    @73
    wunpw
    @70
    @39
    @1
    @72
    @73
    wununi
    @40
    @41
    @1
    prssi
    syl2anc
    @70
    @27
    @1
    @45
    wf
    @46
    @1
    wss
    @70
    vv
    @27
    @44
    @1
    @45
    @70
    @43
    @27
    wcel
    #
    wa
    @39
    @43
    @1
    @70
    @71
    @75
    @72
    adantr
    @70
    @39
    @1
    wcel
    @75
    @73
    adantr
    @70
    @27
    @1
    @43
    @35
    @28
    @69
    simplr
    sselda
    wunpr
    @45
    eqid
    fmptd
    @27
    @1
    @45
    frn
    syl
    unssd
    ralrimiva
    vu
    @27
    @47
    @1
    iunss
    sylibr
    unssd
    eqsstrd
    ex
    expcom
    finds2
    com12
    ralrimiv
    vm
    com
    @3
    @1
    iunss
    sylibr
    syl5eqss
    eqssd
end
