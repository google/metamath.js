include "cn.mm"
include "c3.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cvma.mm"
include "csn.mm"
include "cxp.mm"
include "cprod.mm"
include "csu.mm"
include "c1.mm"
include "cioo.mm"
include "cvts.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "cneg.mm"
include "ce.mm"
include "citg.mm"
include "cexp.mm"
include "wcel.mm"
include "3nn.mm"
include "a1i.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "vmaf.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "nnex.mm"
include "elmapg.mm"
include "mpbir.mm"
include "fconst6.mm"
include "circlemeth.mm"
include "wa.mm"
include "wceq.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "elexi.mm"
include "fvconst2.mm"
include "syl.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "1ex.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "fveq1d.mm"
include "adantl.mm"
include "ssid.mm"
include "cz.mm"
include "nn0zd.mm"
include "adantr.mm"
include "cn0.mm"
include "nnnn0i.mm"
include "simpr.mm"
include "reprf.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "prodfzo03.mm"
include "sumeq2dv.mm"
include "chash.mm"
include "oveq1d.mm"
include "prodeq2dv.mm"
include "cfn.mm"
include "fzofi.mm"
include "ioossre.mm"
include "sstri.mm"
include "sselda.mm"
include "vtscl.mm"
include "fprodconst.mm"
include "syl2anc.mm"
include "hashfzo0.mm"
include "ax-mp.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "itgeq2dv.mm"
include "3eqtr3d.mm"

theorem circlevma
  let wph: wff ph
  let vx: setvar x
  let vn: setvar n
  let cN: class N
  let va: setvar a
  assume circlevma.n: |- ( ph -> N e. NN0 )

  disjoint N n
  disjoint N x
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint N a
  disjoint a n
  disjoint a x
  disjoint a ph
  assert |- ( ph -> sum_ n e. ( NN ( repr ` 3 ) N ) ( ( Lam ` ( n ` 0 ) ) x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) ) = S. ( 0 (,) 1 ) ( ( ( ( Lam vts N ) ` x ) ^ 3 ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x )

  proof
    wph
    cn
    cN
    c3
    crepr
    cfv
    co
    #
    cc0
    c3
    cfzo
    co
    #
    va
    cv
    #
    vn
    cv
    #
    cfv
    #
    @2
    @1
    cvma
    csn
    cxp
    #
    cfv
    #
    cfv
    #
    va
    cprod
    #
    vn
    csu
    vx
    cc0
    c1
    cioo
    co
    #
    @1
    vx
    cv
    #
    @6
    cN
    cvts
    co
    #
    cfv
    #
    va
    cprod
    #
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    cN
    cneg
    @10
    cmul
    co
    cmul
    co
    ce
    cfv
    #
    cmul
    co
    #
    citg
    @0
    cc0
    @3
    cfv
    #
    cvma
    cfv
    #
    c1
    @3
    cfv
    #
    cvma
    cfv
    #
    c2
    @3
    cfv
    #
    cvma
    cfv
    #
    cmul
    co
    cmul
    co
    #
    vn
    csu
    vx
    @9
    @10
    cvma
    cN
    cvts
    co
    #
    cfv
    #
    c3
    cexp
    co
    #
    @14
    cmul
    co
    #
    citg
    wph
    vx
    c3
    @5
    cN
    va
    vn
    circlevma.n
    c3
    cn
    wcel
    wph
    3nn
    a1i
    @1
    cc
    cn
    cmap
    co
    #
    @5
    wf
    wph
    @1
    cvma
    @27
    cvma
    @27
    wcel
    #
    cn
    cc
    cvma
    wf
    #
    cn
    cr
    cvma
    wf
    cr
    cc
    wss
    @29
    vmaf
    ax-resscn
    cn
    cr
    cc
    cvma
    fss
    mp2an
    #
    cc
    cvv
    wcel
    cn
    cvv
    wcel
    @28
    @29
    wb
    cnex
    nnex
    cc
    cn
    cvma
    cvv
    cvv
    elmapg
    mp2an
    mpbir
    #
    fconst6
    a1i
    circlemeth
    wph
    @0
    @8
    @22
    vn
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @17
    @19
    @21
    @7
    va
    @2
    cc0
    wceq
    #
    @4
    @16
    @6
    cvma
    @34
    @2
    @1
    wcel
    #
    @6
    cvma
    wceq
    #
    @34
    @35
    cc0
    @1
    wcel
    cc0
    cc0
    c1
    c2
    ctp
    #
    @1
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    @2
    cc0
    @1
    eleq1
    mpbiri
    @1
    cvma
    @2
    cvma
    @27
    @31
    elexi
    fvconst2
    #
    syl
    @2
    cc0
    @3
    fveq2
    fveq12d
    @2
    c1
    wceq
    #
    @4
    @18
    @6
    cvma
    @39
    @35
    @36
    @39
    @35
    c1
    @1
    wcel
    c1
    @37
    @1
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    @2
    c1
    @1
    eleq1
    mpbiri
    @38
    syl
    @2
    c1
    @3
    fveq2
    fveq12d
    @2
    c2
    wceq
    #
    @4
    @20
    @6
    cvma
    @40
    @35
    @36
    @40
    @35
    c2
    @1
    wcel
    c2
    @37
    @1
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    @2
    c2
    @1
    eleq1
    mpbiri
    @38
    syl
    @2
    c2
    @3
    fveq2
    fveq12d
    @33
    @35
    wa
    #
    @7
    @4
    cvma
    cfv
    #
    cc
    @35
    @7
    @42
    wceq
    @33
    @35
    @4
    @6
    cvma
    @38
    fveq1d
    adantl
    @41
    cn
    cc
    @4
    cvma
    @29
    @41
    @30
    a1i
    @33
    @1
    cn
    @2
    @3
    @33
    cn
    @3
    c3
    cN
    cn
    cn
    wss
    @33
    cn
    ssid
    a1i
    wph
    cN
    cz
    wcel
    @32
    wph
    cN
    circlevma.n
    nn0zd
    adantr
    c3
    cn0
    wcel
    #
    @33
    c3
    3nn
    nnnn0i
    #
    a1i
    wph
    @32
    simpr
    reprf
    ffvelrnda
    ffvelrnd
    eqeltrd
    prodfzo03
    sumeq2dv
    wph
    vx
    @9
    @15
    @26
    wph
    @10
    @9
    wcel
    #
    wa
    #
    @13
    @25
    @14
    cmul
    @46
    @13
    @1
    @24
    va
    cprod
    #
    @24
    @1
    chash
    cfv
    #
    cexp
    co
    #
    @25
    @46
    @1
    @12
    @24
    va
    @46
    @35
    wa
    #
    @10
    @11
    @23
    @50
    @6
    cvma
    cN
    cvts
    @35
    @36
    @46
    @38
    adantl
    oveq1d
    fveq1d
    prodeq2dv
    @46
    @1
    cfn
    wcel
    #
    @24
    cc
    wcel
    @47
    @49
    wceq
    @51
    @46
    cc0
    c3
    fzofi
    a1i
    @46
    cvma
    cN
    @10
    wph
    cN
    cn0
    wcel
    @45
    circlevma.n
    adantr
    wph
    @9
    cc
    @10
    @9
    cc
    wss
    wph
    @9
    cr
    cc
    cc0
    c1
    ioossre
    ax-resscn
    sstri
    a1i
    sselda
    @29
    @46
    @30
    a1i
    vtscl
    @1
    @24
    va
    fprodconst
    syl2anc
    @46
    @48
    c3
    @24
    cexp
    @48
    c3
    wceq
    #
    @46
    @43
    @52
    @44
    c3
    hashfzo0
    ax-mp
    a1i
    oveq2d
    3eqtrd
    oveq1d
    itgeq2dv
    3eqtr3d
end
