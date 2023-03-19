include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "clog.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfz.mm"
include "csu.mm"
include "cmin.mm"
include "cchp.mm"
include "caddc.mm"
include "wss.mm"
include "ioossre.mm"
include "a1i.mm"
include "1red.mm"
include "crp.mm"
include "sselda.mm"
include "1rp.mm"
include "clt.mm"
include "eliooord.mm"
include "adantl.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "recnd.mm"
include "abscld.mm"
include "relogcld.mm"
include "remulcld.mm"
include "2re.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "fzfid.mm"
include "adantr.mm"
include "cn.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "fsumrecl.mm"
include "resubcld.mm"
include "wral.mm"
include "wrex.mm"
include "cmpt.mm"
include "clo1.mm"
include "pntrmax.mm"
include "cvma.mm"
include "cc0.mm"
include "cif.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "simpll.mm"
include "simplr.mm"
include "pntrlog2bndlem6.mm"
include "rexlimdvaa.mm"
include "mpi.mm"
include "chpcl.mm"
include "readdcld.mm"
include "ad2ant2r.mm"
include "simprll.mm"
include "2rp.mm"
include "rpge0d.mm"
include "divge0d.mm"
include "adantlr.mm"
include "cc.mm"
include "absge0d.mm"
include "rpred.mm"
include "nnge1d.mm"
include "logge0d.mm"
include "mulge0d.mm"
include "fsumge0.mm"
include "subge02d.mm"
include "mpbid.mm"
include "wceq.mm"
include "pntrval.mm"
include "fveq2d.mm"
include "abs2dif2d.mm"
include "chpge0.mm"
include "absidd.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "chpwordi.mm"
include "syl3anc.mm"
include "le2addd.mm"
include "letrd.mm"
include "logled.mm"
include "lemul12ad.mm"
include "lediv1dd.mm"
include "addge0d.mm"
include "simprlr.mm"
include "lediv2ad.mm"
include "addcld.mm"
include "mulcld.mm"
include "div1d.mm"
include "lo1bddrp.mm"

theorem pntrlog2bnd
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let cK: class K
  let cN: class N
  let wph: wff ph
  let cE: class E
  let cY: class Y
  assume pntpbnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint n x
  disjoint c n
  disjoint c x
  disjoint R c
  disjoint R n
  disjoint R x
  disjoint a c
  disjoint a n
  disjoint a x
  disjoint A a
  disjoint A c
  disjoint A n
  disjoint A x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint K m
  disjoint n y
  disjoint K n
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint N a
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c y
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint R y
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a y
  disjoint A i
  disjoint A j
  disjoint A m
  disjoint A y
  disjoint E n
  disjoint E y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  assert |- ( ( A e. RR /\ 1 <_ A ) -> E. c e. RR+ A. x e. ( 1 (,) +oo ) ( ( ( ( abs ` ( R ` x ) ) x. ( log ` x ) ) - ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` ( x / A ) ) ) ( ( abs ` ( R ` ( x / n ) ) ) x. ( log ` n ) ) ) ) / x ) <_ c )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    vx
    vy
    c1
    cpnf
    cioo
    co
    #
    vx
    cv
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @4
    clog
    cfv
    #
    cmul
    co
    #
    c2
    @7
    cdiv
    co
    #
    c1
    @4
    cA
    cdiv
    co
    cfl
    cfv
    #
    cfz
    co
    #
    @4
    vn
    cv
    #
    cdiv
    co
    #
    cR
    cfv
    #
    cabs
    cfv
    #
    @12
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cmin
    co
    #
    @4
    cdiv
    co
    #
    c1
    vc
    vy
    cv
    #
    cchp
    cfv
    #
    @22
    caddc
    co
    #
    @22
    clog
    cfv
    #
    cmul
    co
    #
    @3
    cr
    wss
    @2
    c1
    cpnf
    ioossre
    a1i
    #
    @2
    1red
    @2
    @4
    @3
    wcel
    #
    wa
    #
    @20
    @4
    @29
    @8
    @19
    @29
    @6
    @7
    @29
    @5
    @29
    @5
    @29
    @4
    crp
    wcel
    #
    @5
    cr
    wcel
    #
    @29
    @4
    c1
    @2
    @3
    cr
    @4
    @27
    sselda
    #
    c1
    crp
    wcel
    #
    @29
    1rp
    a1i
    @29
    c1
    @4
    @29
    1red
    @32
    @29
    c1
    @4
    clt
    wbr
    #
    @4
    cpnf
    clt
    wbr
    #
    @28
    @34
    @35
    wa
    @2
    @4
    c1
    cpnf
    eliooord
    adantl
    simpld
    #
    ltled
    #
    rpgecld
    #
    crp
    cr
    @4
    cR
    cR
    va
    pntpbnd.r
    pntrf
    #
    ffvelrni
    syl
    #
    recnd
    abscld
    @29
    @4
    @38
    relogcld
    remulcld
    @29
    @9
    @18
    @29
    c2
    @7
    c2
    cr
    wcel
    #
    @29
    2re
    a1i
    @29
    @4
    @32
    @36
    rplogcld
    rerpdivcld
    #
    @29
    @11
    @17
    vn
    @29
    c1
    @10
    fzfid
    @29
    @12
    @11
    wcel
    #
    wa
    #
    @15
    @16
    @44
    @14
    @44
    @14
    @44
    @13
    crp
    wcel
    @14
    cr
    wcel
    @44
    @4
    @12
    @29
    @30
    @43
    @38
    adantr
    @44
    @12
    @43
    @12
    cn
    wcel
    #
    @29
    @12
    @10
    elfznn
    #
    adantl
    nnrpd
    #
    rpdivcld
    crp
    cr
    @13
    cR
    @39
    ffvelrni
    syl
    recnd
    #
    abscld
    @44
    @12
    @47
    relogcld
    remulcld
    #
    fsumrecl
    #
    remulcld
    resubcld
    @38
    rerpdivcld
    #
    @2
    @22
    cR
    cfv
    @22
    cdiv
    co
    cabs
    cfv
    vc
    cv
    #
    cle
    wbr
    vy
    crp
    wral
    #
    vc
    crp
    wrex
    vx
    @3
    @21
    cmpt
    clo1
    wcel
    #
    vy
    cR
    va
    vc
    pntpbnd.r
    pntrmax
    @2
    @53
    @54
    vc
    crp
    @2
    @52
    crp
    wcel
    #
    @53
    wa
    #
    wa
    vx
    vy
    cA
    @52
    cR
    va
    cr
    c1
    va
    cv
    #
    cfl
    cfv
    cfz
    co
    vi
    cv
    #
    cvma
    cfv
    @58
    clog
    cfv
    @57
    @58
    cdiv
    co
    cchp
    cfv
    caddc
    co
    cmul
    co
    vi
    csu
    cmpt
    #
    va
    cr
    @57
    crp
    wcel
    @57
    @57
    clog
    cfv
    cmul
    co
    cc0
    cif
    cmpt
    #
    vi
    vn
    va
    @59
    eqid
    pntpbnd.r
    @60
    eqid
    @2
    @55
    @53
    simprl
    @2
    @55
    @53
    simprr
    @0
    @1
    @56
    simpll
    @0
    @1
    @56
    simplr
    pntrlog2bndlem6
    rexlimdvaa
    mpi
    @2
    @22
    cr
    wcel
    #
    c1
    @22
    cle
    wbr
    #
    wa
    #
    wa
    #
    @24
    @25
    @64
    @23
    @22
    @64
    @61
    @23
    cr
    wcel
    #
    @2
    @61
    @62
    simprl
    #
    @22
    chpcl
    syl
    #
    @66
    readdcld
    @64
    @22
    @64
    @22
    c1
    @66
    @33
    @64
    1rp
    a1i
    @2
    @61
    @62
    simprr
    rpgecld
    #
    relogcld
    remulcld
    @29
    @63
    @4
    @22
    clt
    wbr
    #
    wa
    #
    wa
    #
    @21
    @26
    @4
    cdiv
    co
    #
    @26
    @29
    @21
    cr
    wcel
    @70
    @51
    adantr
    @71
    @26
    @4
    @71
    @24
    @25
    @71
    @23
    @22
    @2
    @63
    @65
    @28
    @69
    @67
    ad2ant2r
    #
    @29
    @61
    @62
    @69
    simprll
    #
    readdcld
    #
    @71
    @22
    @2
    @63
    @22
    crp
    wcel
    @28
    @69
    @68
    ad2ant2r
    #
    relogcld
    #
    remulcld
    #
    @29
    @30
    @70
    @38
    adantr
    #
    rerpdivcld
    @78
    @71
    @20
    @26
    @4
    @71
    @8
    @19
    @71
    @6
    @7
    @71
    @5
    @71
    @5
    @29
    @31
    @70
    @40
    adantr
    recnd
    #
    abscld
    #
    @71
    @4
    @79
    relogcld
    #
    remulcld
    #
    @71
    @9
    @18
    @29
    @9
    cr
    wcel
    @70
    @42
    adantr
    #
    @29
    @18
    cr
    wcel
    @70
    @50
    adantr
    #
    remulcld
    #
    resubcld
    #
    @78
    @79
    @71
    @20
    @8
    @26
    @87
    @83
    @78
    @71
    cc0
    @19
    cle
    wbr
    @20
    @8
    cle
    wbr
    @71
    @9
    @18
    @84
    @85
    @71
    c2
    @7
    @41
    @71
    2re
    a1i
    @71
    @4
    @29
    @4
    cr
    wcel
    #
    @70
    @32
    adantr
    #
    @29
    @34
    @70
    @36
    adantr
    rplogcld
    #
    @71
    c2
    c2
    crp
    wcel
    @71
    2rp
    a1i
    rpge0d
    divge0d
    @71
    @11
    @17
    vn
    @71
    c1
    @10
    fzfid
    @29
    @43
    @17
    cr
    wcel
    @70
    @49
    adantlr
    @71
    @43
    wa
    #
    @15
    @16
    @91
    @14
    @29
    @43
    @14
    cc
    wcel
    @70
    @48
    adantlr
    #
    abscld
    @91
    @12
    @29
    @43
    @12
    crp
    wcel
    @70
    @47
    adantlr
    #
    relogcld
    @91
    @14
    @92
    absge0d
    @91
    @12
    @91
    @12
    @93
    rpred
    @91
    @12
    @43
    @45
    @71
    @46
    adantl
    nnge1d
    logge0d
    mulge0d
    fsumge0
    mulge0d
    @71
    @8
    @19
    @83
    @86
    subge02d
    mpbid
    @71
    @6
    @24
    @7
    @25
    @81
    @75
    @82
    @77
    @71
    @5
    @80
    absge0d
    @71
    @7
    @90
    rpge0d
    @71
    @6
    @4
    cchp
    cfv
    #
    @4
    caddc
    co
    #
    @24
    @81
    @71
    @94
    @4
    @71
    @88
    @94
    cr
    wcel
    @89
    @4
    chpcl
    syl
    #
    @89
    readdcld
    @75
    @71
    @6
    @94
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @95
    cle
    @71
    @5
    @97
    cabs
    @71
    @30
    @5
    @97
    wceq
    @79
    @4
    cR
    va
    pntpbnd.r
    pntrval
    syl
    fveq2d
    @71
    @98
    @94
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    caddc
    co
    @95
    cle
    @71
    @94
    @4
    @71
    @94
    @96
    recnd
    @71
    @4
    @89
    recnd
    abs2dif2d
    @71
    @99
    @94
    @100
    @4
    caddc
    @71
    @94
    @96
    @71
    @88
    cc0
    @94
    cle
    wbr
    @89
    @4
    chpge0
    syl
    absidd
    @71
    @4
    @89
    @71
    @4
    @79
    rpge0d
    absidd
    oveq12d
    breqtrd
    eqbrtrd
    @71
    @94
    @4
    @23
    @22
    @96
    @89
    @73
    @74
    @71
    @88
    @61
    @4
    @22
    cle
    wbr
    #
    @94
    @23
    cle
    wbr
    @89
    @74
    @71
    @4
    @22
    @89
    @74
    @29
    @63
    @69
    simprr
    ltled
    #
    @4
    @22
    chpwordi
    syl3anc
    @102
    le2addd
    letrd
    @71
    @101
    @7
    @25
    cle
    wbr
    @102
    @71
    @4
    @22
    @79
    @76
    logled
    mpbid
    lemul12ad
    letrd
    lediv1dd
    @71
    @72
    @26
    c1
    cdiv
    co
    @26
    cle
    @71
    c1
    @4
    @26
    @33
    @71
    1rp
    a1i
    @79
    @78
    @71
    @24
    @25
    @75
    @77
    @71
    @23
    @22
    @73
    @74
    @71
    @61
    cc0
    @23
    cle
    wbr
    @74
    @22
    chpge0
    syl
    @71
    @22
    @76
    rpge0d
    addge0d
    @71
    @22
    @74
    @29
    @61
    @62
    @69
    simprlr
    logge0d
    mulge0d
    @29
    c1
    @4
    cle
    wbr
    @70
    @37
    adantr
    lediv2ad
    @71
    @26
    @71
    @24
    @25
    @71
    @23
    @22
    @71
    @23
    @73
    recnd
    @71
    @22
    @74
    recnd
    addcld
    @71
    @25
    @77
    recnd
    mulcld
    div1d
    breqtrd
    letrd
    lo1bddrp
end
