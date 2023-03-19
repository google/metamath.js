include "cc0.mm"
include "cn.mm"
include "c3.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "cmul.mm"
include "c1.mm"
include "c2.mm"
include "csu.mm"
include "cprime.mm"
include "cin.mm"
include "cdif.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "c4.mm"
include "c8.mm"
include "cdp2.mm"
include "cdp.mm"
include "cexp.mm"
include "cfn.mm"
include "wcel.mm"
include "tgoldbachgnn.mm"
include "nnnn0d.mm"
include "cn0.mm"
include "3nn0.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "reprfi2.mm"
include "diffi.mm"
include "syl.mm"
include "cr.mm"
include "difssd.mm"
include "sselda.mm"
include "wa.mm"
include "wf.mm"
include "vmaf.mm"
include "cfzo.mm"
include "cz.mm"
include "nn0zd.mm"
include "adantr.mm"
include "simpr.mm"
include "reprf.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "ffvelrnd.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "remulcld.mm"
include "1ex.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "syldan.mm"
include "fsumrecl.mm"
include "0nn0.mm"
include "cq.mm"
include "qssre.mm"
include "4nn0.mm"
include "2nn0.mm"
include "nn0ssq.mm"
include "8nn0.mm"
include "sselii.mm"
include "dp2clq.mm"
include "dpcl.mm"
include "mp2an.mm"
include "nnred.mm"
include "resqcld.mm"
include "c7.mm"
include "clog.mm"
include "csqrt.mm"
include "cdiv.mm"
include "7nn0.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nn0ge0d.mm"
include "resqrtcld.mm"
include "sqrtgt0d.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "hgt750leme.mm"
include "2z.mm"
include "rpexpcld.mm"
include "cdc.mm"
include "cle.mm"
include "hgt750lem.mm"
include "syl2anc.mm"
include "ltmul1dd.mm"
include "lelttrd.mm"
include "cioo.mm"
include "cof.mm"
include "cvts.mm"
include "ci.mm"
include "cpi.mm"
include "cneg.mm"
include "ce.mm"
include "citg.mm"
include "circlemethhgt.mm"
include "breqtrrd.mm"
include "ltletrd.mm"
include "posdifd.mm"
include "mpbid.mm"
include "inss2.mm"
include "prmssnn.mm"
include "sstri.mm"
include "reprss.mm"
include "ssfid.mm"
include "cc.mm"
include "recnd.mm"
include "fsumcl.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "cun.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "fsumsplit.mm"
include "mvrraddd.mm"
include "breqtrd.mm"

theorem tgoldbachgtde
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  assume tgoldbachgtda.o: |- O = { z e. ZZ | -. 2 || z }
  assume tgoldbachgtda.n: |- ( ph -> N e. O )
  assume tgoldbachgtda.0: |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N )
  assume tgoldbachgtda.h: |- ( ph -> H : NN --> ( 0 [,) +oo ) )
  assume tgoldbachgtda.k: |- ( ph -> K : NN --> ( 0 [,) +oo ) )
  assume tgoldbachgtda.1: |- ( ( ph /\ m e. NN ) -> ( K ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 ) )
  assume tgoldbachgtda.2: |- ( ( ph /\ m e. NN ) -> ( H ` m ) <_ ( 1 . _ 4 _ 1 4 ) )
  assume tgoldbachgtda.3: |- ( ph -> ( ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) x. ( N ^ 2 ) ) <_ S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. H ) vts N ) ` x ) x. ( ( ( ( Lam oF x. K ) vts N ) ` x ) ^ 2 ) ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x )

  disjoint H m
  disjoint H n
  disjoint H x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N z
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint O m
  disjoint O n
  disjoint O z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> 0 < sum_ n e. ( ( O i^i Prime ) ( repr ` 3 ) N ) ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) ) x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) ) x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) ) )

  proof
    wph
    cc0
    cn
    cN
    c3
    crepr
    cfv
    #
    co
    #
    cc0
    vn
    cv
    #
    cfv
    #
    cvma
    cfv
    #
    @3
    cH
    cfv
    #
    cmul
    co
    #
    c1
    @2
    cfv
    #
    cvma
    cfv
    #
    @7
    cK
    cfv
    #
    cmul
    co
    #
    c2
    @2
    cfv
    #
    cvma
    cfv
    #
    @11
    cK
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @1
    cO
    cprime
    cin
    #
    cN
    @0
    co
    #
    cdif
    #
    @16
    vn
    csu
    #
    cmin
    co
    #
    @19
    @16
    vn
    csu
    #
    clt
    wph
    @21
    @17
    clt
    wbr
    cc0
    @22
    clt
    wbr
    wph
    @21
    cc0
    cc0
    cc0
    cc0
    c4
    c2
    c2
    c4
    c8
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp
    co
    #
    cN
    c2
    cexp
    co
    #
    cmul
    co
    #
    @17
    wph
    @20
    @16
    vn
    wph
    @1
    cfn
    wcel
    @20
    cfn
    wcel
    wph
    cn
    c3
    cN
    wph
    cN
    wph
    vz
    cN
    cO
    tgoldbachgtda.o
    tgoldbachgtda.n
    tgoldbachgtda.0
    tgoldbachgnn
    #
    nnnn0d
    #
    c3
    cn0
    wcel
    #
    wph
    3nn0
    a1i
    #
    cn
    cn
    wss
    #
    wph
    cn
    ssid
    #
    a1i
    #
    reprfi2
    #
    @1
    @19
    diffi
    syl
    wph
    @2
    @20
    wcel
    @2
    @1
    wcel
    #
    @16
    cr
    wcel
    wph
    @20
    @1
    @2
    wph
    @1
    @19
    difssd
    sselda
    wph
    @42
    wa
    #
    @6
    @15
    @43
    @4
    @5
    @43
    cn
    cr
    @3
    cvma
    cn
    cr
    cvma
    wf
    @43
    vmaf
    a1i
    #
    @43
    cc0
    c3
    cfzo
    co
    #
    cn
    cc0
    @2
    @43
    cn
    @2
    c3
    cN
    @38
    @43
    @39
    a1i
    wph
    cN
    cz
    wcel
    @42
    wph
    cN
    @35
    nn0zd
    #
    adantr
    @36
    @43
    3nn0
    a1i
    wph
    @42
    simpr
    reprf
    #
    cc0
    @45
    wcel
    @43
    cc0
    cc0
    c1
    c2
    ctp
    #
    @45
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    #
    ffvelrnd
    @43
    cn
    cr
    @3
    cH
    wph
    cn
    cr
    cH
    wf
    #
    @42
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    cH
    wf
    @51
    cr
    wss
    #
    @50
    tgoldbachgtda.h
    rge0ssre
    cn
    @51
    cr
    cH
    fss
    sylancl
    #
    adantr
    @49
    ffvelrnd
    remulcld
    @43
    @10
    @14
    @43
    @8
    @9
    @43
    cn
    cr
    @7
    cvma
    @44
    @43
    @45
    cn
    c1
    @2
    @47
    c1
    @45
    wcel
    @43
    c1
    @48
    @45
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    #
    ffvelrnd
    @43
    cn
    cr
    @7
    cK
    wph
    cn
    cr
    cK
    wf
    #
    @42
    wph
    cn
    @51
    cK
    wf
    @52
    @55
    tgoldbachgtda.k
    rge0ssre
    cn
    @51
    cr
    cK
    fss
    sylancl
    #
    adantr
    #
    @54
    ffvelrnd
    remulcld
    @43
    @12
    @13
    @43
    cn
    cr
    @11
    cvma
    @44
    @43
    @45
    cn
    c2
    @2
    @47
    c2
    @45
    wcel
    @43
    c2
    @48
    @45
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    #
    ffvelrnd
    @43
    cn
    cr
    @11
    cK
    @57
    @58
    ffvelrnd
    remulcld
    remulcld
    remulcld
    #
    syldan
    fsumrecl
    #
    wph
    @31
    @32
    @31
    cr
    wcel
    #
    wph
    cc0
    cn0
    wcel
    @30
    cr
    wcel
    @61
    0nn0
    cq
    cr
    @30
    qssre
    cc0
    @29
    0nn0
    cc0
    @28
    0nn0
    cc0
    @27
    0nn0
    c4
    @26
    4nn0
    c2
    @25
    2nn0
    c2
    @24
    2nn0
    c4
    c8
    4nn0
    cn0
    cq
    c8
    nn0ssq
    8nn0
    sselii
    dp2clq
    #
    dp2clq
    dp2clq
    dp2clq
    dp2clq
    dp2clq
    dp2clq
    sselii
    cc0
    @30
    dpcl
    mp2an
    a1i
    #
    wph
    cN
    wph
    cN
    @34
    nnred
    #
    resqcld
    #
    remulcld
    #
    wph
    @1
    @16
    vn
    @41
    @59
    fsumrecl
    #
    wph
    @21
    c7
    c3
    @24
    cdp2
    #
    cdp
    co
    #
    cN
    clog
    cfv
    #
    cN
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    @32
    cmul
    co
    @33
    @60
    wph
    @73
    @32
    wph
    @69
    @72
    @69
    cr
    wcel
    #
    wph
    c7
    cn0
    wcel
    @68
    cr
    wcel
    @74
    7nn0
    cq
    cr
    @68
    qssre
    c3
    @24
    3nn0
    @62
    dp2clq
    sselii
    c7
    @68
    dpcl
    mp2an
    a1i
    wph
    @70
    @71
    wph
    cN
    wph
    cN
    @34
    nnrpd
    #
    relogcld
    wph
    cN
    @64
    wph
    cN
    @35
    nn0ge0d
    resqrtcld
    wph
    @71
    wph
    cN
    @75
    sqrtgt0d
    gt0ne0d
    redivcld
    remulcld
    #
    @65
    remulcld
    @66
    wph
    vz
    vm
    vn
    cH
    cK
    cN
    cO
    tgoldbachgtda.o
    @34
    tgoldbachgtda.0
    tgoldbachgtda.h
    tgoldbachgtda.k
    tgoldbachgtda.1
    tgoldbachgtda.2
    hgt750leme
    wph
    @73
    @31
    @32
    @76
    @63
    wph
    cN
    c2
    @75
    c2
    cz
    wcel
    wph
    2z
    a1i
    rpexpcld
    wph
    cN
    cn0
    wcel
    c1
    cc0
    cdc
    c2
    c7
    cdc
    cexp
    co
    cN
    cle
    wbr
    @73
    @31
    clt
    wbr
    @35
    tgoldbachgtda.0
    cN
    hgt750lem
    syl2anc
    ltmul1dd
    lelttrd
    wph
    @33
    vx
    cc0
    c1
    cioo
    co
    vx
    cv
    #
    cvma
    cH
    cmul
    cof
    #
    co
    cN
    cvts
    co
    cfv
    @77
    cvma
    cK
    @78
    co
    cN
    cvts
    co
    cfv
    c2
    cexp
    co
    cmul
    co
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    cN
    cneg
    @77
    cmul
    co
    cmul
    co
    ce
    cfv
    cmul
    co
    citg
    @17
    cle
    tgoldbachgtda.3
    wph
    vx
    vn
    cH
    cK
    cN
    @53
    @56
    @35
    circlemethhgt
    breqtrrd
    ltletrd
    wph
    @21
    @17
    @60
    @67
    posdifd
    mpbid
    wph
    @17
    @23
    @21
    wph
    @19
    @16
    vn
    wph
    @1
    @19
    @41
    wph
    cn
    @18
    c3
    cN
    @40
    @46
    @37
    @18
    cn
    wss
    wph
    @18
    cprime
    cn
    cO
    cprime
    inss2
    prmssnn
    sstri
    a1i
    reprss
    #
    ssfid
    wph
    @2
    @19
    wcel
    @42
    @16
    cc
    wcel
    wph
    @19
    @1
    @2
    @79
    sselda
    @43
    @16
    @59
    recnd
    #
    syldan
    fsumcl
    wph
    @21
    @60
    recnd
    wph
    @19
    @20
    @16
    @1
    vn
    @19
    @20
    cin
    c0
    wceq
    wph
    @19
    @1
    disjdif
    a1i
    wph
    @19
    @20
    cun
    #
    @1
    wph
    @19
    @1
    wss
    @81
    @1
    wceq
    @79
    @19
    @1
    undif
    sylib
    eqcomd
    @41
    @80
    fsumsplit
    mvrraddd
    breqtrd
end
