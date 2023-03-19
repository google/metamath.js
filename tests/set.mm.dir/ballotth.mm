include "cfv.mm"
include "c1.mm"
include "cdif.mm"
include "chash.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "c2.mm"
include "caddc.mm"
include "cmul.mm"
include "wss.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfz.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cpw.mm"
include "wcel.mm"
include "cfn.mm"
include "fzfi.mm"
include "pwfi.mm"
include "mpbi.mm"
include "ssfi.mm"
include "mp2an.mm"
include "elexi.mm"
include "elpw.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylbir.mm"
include "ax-mp.mm"
include "hashssdif.mm"
include "eqcomi.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cni.mm"
include "difss.mm"
include "subsub23i.mm"
include "oveq1i.mm"
include "eqtr4i.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "cbc.mm"
include "ballotlem1.mm"
include "cn.mm"
include "cle.mm"
include "nnnn0i.mm"
include "nnaddcl.mm"
include "nnrei.mm"
include "nn0addge1i.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "bccl2.mm"
include "nnne0i.mm"
include "eqnetri.mm"
include "pm3.2i.mm"
include "divsubdir.mm"
include "mp3an.mm"
include "dividi.mm"
include "3eqtri.mm"
include "wn.mm"
include "ballotlem8.mm"
include "cun.mm"
include "rabxm.mm"
include "fveq2i.mm"
include "cin.mm"
include "c0.mm"
include "sstri.mm"
include "rabnc.mm"
include "hashun.mm"
include "eqtri.mm"
include "elpw2.mm"
include "mpbir.mm"
include "ballotlem2.mm"
include "wi.mm"
include "nfrab1.mm"
include "dfss2f.mm"
include "ballotlem4.mm"
include "imdistani.mm"
include "rabid.mm"
include "eldif.mm"
include "3imtr4i.mm"
include "simprbi.mm"
include "sylanbrc.mm"
include "mpgbir.mm"
include "rabss2.mm"
include "eqssi.mm"
include "3eqtr3i.mm"
include "oveq2i.mm"
include "2cn.mm"
include "divassi.mm"
include "2timesi.mm"
include "3eqtr2i.mm"
include "3eqtr4ri.mm"
include "nncni.mm"
include "mulcli.mm"
include "addsub4i.mm"
include "subidi.mm"
include "subcli.mm"
include "addid1i.mm"
include "oveq12i.mm"
include "3eqtr3ri.mm"

theorem ballotth
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let cC: class C
  let vd: setvar d
  let cJ: class J
  let cD: class D
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )
  assume ballotth.r: |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) )

  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint R k
  disjoint c x
  disjoint F x
  disjoint M x
  disjoint N x
  disjoint k x
  disjoint i x
  disjoint E x
  disjoint O x
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint C i
  disjoint C k
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint J k
  disjoint D i
  disjoint D k
  disjoint C x
  disjoint S d
  assert |- ( P ` E ) = ( ( M - N ) / ( M + N ) )

  proof
    cE
    cP
    cfv
    #
    c1
    cO
    cE
    cdif
    #
    chash
    cfv
    #
    cO
    chash
    cfv
    #
    cdiv
    co
    #
    cmin
    co
    #
    c1
    c2
    cN
    cM
    cN
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cM
    cN
    cmin
    co
    #
    @6
    cdiv
    co
    #
    @0
    @3
    @2
    cmin
    co
    #
    @3
    cdiv
    co
    #
    @3
    @3
    cdiv
    co
    #
    @4
    cmin
    co
    #
    @5
    @0
    cE
    chash
    cfv
    #
    @3
    cdiv
    co
    #
    @13
    cE
    cO
    wss
    #
    @0
    @17
    wceq
    #
    cE
    cc0
    vi
    cv
    vc
    cv
    #
    cF
    cfv
    cfv
    clt
    wbr
    vi
    c1
    @6
    cfz
    co
    #
    wral
    #
    vc
    cO
    crab
    cO
    ballotth.e
    @22
    vc
    cO
    ssrab2
    eqsstri
    #
    @18
    cE
    cO
    cpw
    #
    wcel
    @19
    cE
    cO
    cE
    cfn
    cO
    cfn
    wcel
    #
    @18
    cE
    cfn
    wcel
    #
    @21
    cpw
    #
    cfn
    wcel
    #
    cO
    @27
    wss
    @25
    @21
    cfn
    wcel
    @28
    c1
    @6
    fzfi
    @21
    pwfi
    mpbi
    #
    cO
    @20
    chash
    cfv
    cM
    wceq
    #
    vc
    @27
    crab
    @27
    ballotth.o
    @30
    vc
    @27
    ssrab2
    eqsstri
    #
    @27
    cO
    ssfi
    mp2an
    #
    @23
    cO
    cE
    ssfi
    mp2an
    #
    elexi
    elpw
    vx
    cE
    vx
    cv
    #
    chash
    cfv
    #
    @3
    cdiv
    co
    #
    @17
    @24
    cP
    @34
    cE
    wceq
    @35
    @16
    @3
    cdiv
    @34
    cE
    chash
    fveq2
    oveq1d
    ballotth.p
    @16
    @3
    cdiv
    ovex
    fvmpt
    sylbir
    ax-mp
    @12
    @16
    @3
    cdiv
    @3
    @16
    cmin
    co
    #
    @2
    wceq
    @12
    @16
    wceq
    @2
    @37
    @25
    @18
    @2
    @37
    wceq
    @32
    @23
    cO
    cE
    hashssdif
    mp2an
    eqcomi
    @3
    @16
    @2
    @3
    @25
    @3
    cn0
    wcel
    @32
    cO
    hashcl
    ax-mp
    nn0cni
    #
    @16
    @26
    @16
    cn0
    wcel
    @33
    cE
    hashcl
    ax-mp
    nn0cni
    @2
    @1
    cfn
    wcel
    #
    @2
    cn0
    wcel
    @25
    @1
    cO
    wss
    #
    @39
    @32
    cO
    cE
    difss
    #
    cO
    @1
    ssfi
    mp2an
    @1
    hashcl
    ax-mp
    nn0cni
    #
    subsub23i
    mpbi
    oveq1i
    eqtr4i
    @3
    cc
    wcel
    #
    @2
    cc
    wcel
    @43
    @3
    cc0
    wne
    #
    wa
    @13
    @15
    wceq
    @38
    @42
    @43
    @44
    @38
    @3
    @6
    cM
    cbc
    co
    #
    cc0
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlem1
    @45
    cM
    cc0
    @6
    cfz
    co
    wcel
    #
    @45
    cn
    wcel
    @46
    cM
    cn0
    wcel
    @6
    cn0
    wcel
    cM
    @6
    cle
    wbr
    cM
    ballotth.m
    nnnn0i
    @6
    cM
    cn
    wcel
    cN
    cn
    wcel
    @6
    cn
    wcel
    ballotth.m
    ballotth.n
    cM
    cN
    nnaddcl
    mp2an
    #
    nnnn0i
    cM
    cN
    cM
    ballotth.m
    nnrei
    cN
    ballotth.n
    nnnn0i
    nn0addge1i
    cM
    @6
    elfz2nn0
    mpbir3an
    cM
    @6
    bccl2
    ax-mp
    nnne0i
    eqnetri
    #
    pm3.2i
    @3
    @2
    @3
    divsubdir
    mp3an
    @14
    c1
    @4
    cmin
    @3
    @38
    @48
    dividi
    oveq1i
    3eqtri
    @8
    @4
    c1
    cmin
    c1
    @20
    wcel
    #
    vc
    @1
    crab
    #
    chash
    cfv
    #
    @49
    wn
    #
    vc
    @1
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    @3
    cdiv
    co
    @54
    @54
    caddc
    co
    #
    @3
    cdiv
    co
    #
    @4
    @8
    @55
    @56
    @3
    cdiv
    @51
    @54
    @54
    caddc
    vx
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlem8
    oveq1i
    oveq1i
    @2
    @55
    @3
    cdiv
    @2
    @50
    @53
    cun
    #
    chash
    cfv
    #
    @55
    @1
    @58
    chash
    @49
    vc
    @1
    rabxm
    fveq2i
    @50
    cfn
    wcel
    #
    @53
    cfn
    wcel
    #
    @50
    @53
    cin
    c0
    wceq
    @59
    @55
    wceq
    @28
    @50
    @27
    wss
    @60
    @29
    @50
    cO
    @27
    @50
    @1
    cO
    @49
    vc
    @1
    ssrab2
    @41
    sstri
    @31
    sstri
    @27
    @50
    ssfi
    mp2an
    @28
    @53
    @27
    wss
    @61
    @29
    @53
    cO
    @27
    @53
    @1
    cO
    @52
    vc
    @1
    ssrab2
    @41
    sstri
    @31
    sstri
    @27
    @53
    ssfi
    mp2an
    #
    @49
    vc
    @1
    rabnc
    @50
    @53
    hashun
    mp3an
    eqtri
    oveq1i
    @8
    c2
    @54
    @3
    cdiv
    co
    #
    cmul
    co
    c2
    @54
    cmul
    co
    #
    @3
    cdiv
    co
    @57
    @7
    @63
    c2
    cmul
    @52
    vc
    cO
    crab
    #
    cP
    cfv
    #
    @65
    chash
    cfv
    #
    @3
    cdiv
    co
    #
    @7
    @63
    @65
    @24
    wcel
    #
    @66
    @68
    wceq
    @69
    @65
    cO
    wss
    @52
    vc
    cO
    ssrab2
    @65
    cO
    cO
    cfn
    @32
    elexi
    elpw2
    mpbir
    vx
    @65
    @36
    @68
    @24
    cP
    @34
    @65
    wceq
    @35
    @67
    @3
    cdiv
    @34
    @65
    chash
    fveq2
    oveq1d
    ballotth.p
    @67
    @3
    cdiv
    ovex
    fvmpt
    ax-mp
    vx
    cP
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotlem2
    @67
    @54
    @3
    cdiv
    @65
    @53
    chash
    @65
    @53
    @65
    @53
    wss
    @20
    @65
    wcel
    #
    @20
    @53
    wcel
    #
    wi
    vc
    vc
    @65
    @53
    @52
    vc
    cO
    nfrab1
    @52
    vc
    @1
    nfrab1
    dfss2f
    @70
    @20
    @1
    wcel
    #
    @52
    @71
    @20
    cO
    wcel
    #
    @52
    wa
    @73
    @20
    cE
    wcel
    wn
    #
    wa
    @70
    @72
    @73
    @52
    @74
    vx
    @20
    cP
    vi
    cE
    cF
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotlem4
    imdistani
    @52
    vc
    cO
    rabid
    #
    @20
    cO
    cE
    eldif
    3imtr4i
    @70
    @73
    @52
    @75
    simprbi
    @52
    vc
    @1
    rabid
    sylanbrc
    mpgbir
    @40
    @53
    @65
    wss
    @41
    @52
    vc
    @1
    cO
    rabss2
    ax-mp
    eqssi
    fveq2i
    oveq1i
    3eqtr3i
    oveq2i
    c2
    @54
    @3
    2cn
    @54
    @61
    @54
    cn0
    wcel
    @62
    @53
    hashcl
    ax-mp
    nn0cni
    #
    @38
    @48
    divassi
    @64
    @56
    @3
    cdiv
    @54
    @76
    2timesi
    oveq1i
    3eqtr2i
    3eqtr4ri
    oveq2i
    @6
    c2
    cN
    cmul
    co
    #
    cmin
    co
    #
    @6
    cdiv
    co
    #
    @6
    @6
    cdiv
    co
    #
    @77
    @6
    cdiv
    co
    #
    cmin
    co
    #
    @11
    @9
    @6
    cc
    wcel
    #
    @77
    cc
    wcel
    @83
    @6
    cc0
    wne
    #
    wa
    @79
    @82
    wceq
    @6
    @47
    nncni
    #
    c2
    cN
    2cn
    cN
    ballotth.n
    nncni
    #
    mulcli
    @83
    @84
    @85
    @6
    @47
    nnne0i
    #
    pm3.2i
    @6
    @77
    @6
    divsubdir
    mp3an
    @78
    @10
    @6
    cdiv
    @78
    @6
    cN
    cN
    caddc
    co
    #
    cmin
    co
    #
    @10
    @77
    @88
    @6
    cmin
    cN
    @86
    2timesi
    oveq2i
    @89
    @10
    cN
    cN
    cmin
    co
    #
    caddc
    co
    @10
    cc0
    caddc
    co
    @10
    cM
    cN
    cN
    cN
    cM
    ballotth.m
    nncni
    #
    @86
    @86
    @86
    addsub4i
    @90
    cc0
    @10
    caddc
    cN
    @86
    subidi
    oveq2i
    @10
    cM
    cN
    @91
    @86
    subcli
    addid1i
    3eqtri
    eqtri
    oveq1i
    @80
    c1
    @81
    @8
    cmin
    @6
    @85
    @87
    dividi
    c2
    cN
    @6
    2cn
    @86
    @85
    @87
    divassi
    oveq12i
    3eqtr3ri
    3eqtr2i
end
