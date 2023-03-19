include "cr.mm"
include "cply.mm"
include "cfv.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cidp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "cn0.mm"
include "cv.mm"
include "cmpt.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "wf.mm"
include "eldifi.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "1re.mm"
include "plyid.mm"
include "mp2an.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "readdcld.mm"
include "remulcld.mm"
include "plymul.mm"
include "0re.mm"
include "eqid.mm"
include "coef2.mm"
include "sylancl.mm"
include "feqmptd.mm"
include "cvv.mm"
include "cnex.mm"
include "plyf.mm"
include "syl.mm"
include "ax-mp.mm"
include "mulcomd.mm"
include "caofcom.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cfz.mm"
include "csu.mm"
include "simpr.mm"
include "coemul.mm"
include "syl3anc.mm"
include "elfznn0.mm"
include "coeidp.mm"
include "oveq1d.mm"
include "ovif.mm"
include "syl6eq.mm"
include "adantl.mm"
include "sumeq2dv.mm"
include "wb.mm"
include "velsn.mm"
include "bicomi.mm"
include "ad2antrr.mm"
include "fznn0sub.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "mulid2d.mm"
include "mul02d.mm"
include "ifbieq12d.mm"
include "eqeq2.mm"
include "oveq2.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "wn.mm"
include "elsni.mm"
include "ax-1ne0.mm"
include "nesymi.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "notbii.mm"
include "biimpi.mm"
include "iffalse.mm"
include "3syl.mm"
include "sumeq12rdv.mm"
include "cuz.mm"
include "cfn.mm"
include "wo.mm"
include "snfi.mm"
include "olci.mm"
include "sumz.mm"
include "cn.mm"
include "simpll.mm"
include "wne.mm"
include "neqned.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "wral.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "nnnn0d.mm"
include "nnge1d.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "snssd.mm"
include "sylbi.mm"
include "nnm1nn0.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "fzfi.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "sumsn.mm"
include "sylancr.mm"
include "eqtr3d.mm"
include "syl2anc.mm"
include "ifbothda.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"

theorem plymulx0
  let vn: setvar n
  let cF: class F
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y

  disjoint F n
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint F x
  disjoint F y
  assert |- ( F e. ( ( Poly ` RR ) \ { 0p } ) -> ( coeff ` ( F oF x. Xp ) ) = ( n e. NN0 |-> if ( n = 0 , 0 , ( ( coeff ` F ) ` ( n - 1 ) ) ) ) )

  proof
    cF
    cr
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    wcel
    #
    cF
    cidp
    cmul
    cof
    #
    co
    #
    ccoe
    cfv
    #
    vn
    cn0
    vn
    cv
    #
    @5
    cfv
    #
    cmpt
    vn
    cn0
    @6
    cc0
    wceq
    #
    cc0
    @6
    c1
    cmin
    co
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    cif
    #
    cmpt
    @2
    vn
    cn0
    cr
    @5
    @2
    @4
    @0
    wcel
    cc0
    cr
    wcel
    #
    cn0
    cr
    @5
    wf
    @2
    vx
    vy
    cr
    cF
    cidp
    cF
    @0
    @1
    eldifi
    #
    cidp
    @0
    wcel
    #
    @2
    cr
    cc
    wss
    c1
    cr
    wcel
    #
    @15
    ax-resscn
    1re
    cr
    plyid
    mp2an
    #
    a1i
    @2
    vx
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    wa
    wa
    #
    @18
    @20
    @2
    @19
    @21
    simprl
    #
    @2
    @19
    @21
    simprr
    #
    readdcld
    @22
    @18
    @20
    @23
    @24
    remulcld
    plymul
    0re
    @5
    cr
    @4
    @5
    eqid
    coef2
    sylancl
    feqmptd
    @2
    vn
    cn0
    @7
    @12
    @2
    @6
    cn0
    wcel
    #
    wa
    #
    @7
    @6
    cidp
    cF
    @3
    co
    #
    ccoe
    cfv
    #
    cfv
    #
    @12
    @2
    @7
    @29
    wceq
    @25
    @2
    @6
    @5
    @28
    @2
    @4
    @27
    ccoe
    @2
    vx
    vy
    cc
    cmul
    cc
    cF
    cidp
    cvv
    cc
    cvv
    wcel
    @2
    cnex
    a1i
    @2
    cF
    @0
    wcel
    #
    cc
    cc
    cF
    wf
    @14
    cr
    cF
    plyf
    syl
    cc
    cc
    cidp
    wf
    #
    @2
    @15
    @31
    @17
    cr
    cidp
    plyf
    ax-mp
    a1i
    @2
    @18
    cc
    wcel
    #
    @20
    cc
    wcel
    #
    wa
    wa
    @18
    @20
    @2
    @32
    @33
    simprl
    @2
    @32
    @33
    simprr
    mulcomd
    caofcom
    fveq2d
    fveq1d
    adantr
    @26
    @29
    cc0
    @6
    cfz
    co
    #
    vi
    cv
    #
    cidp
    ccoe
    cfv
    #
    cfv
    #
    @6
    @35
    cmin
    co
    #
    @10
    cfv
    #
    cmul
    co
    #
    vi
    csu
    #
    @34
    @35
    c1
    wceq
    #
    c1
    @39
    cmul
    co
    #
    cc0
    @39
    cmul
    co
    #
    cif
    #
    vi
    csu
    #
    @12
    @26
    @15
    @30
    @25
    @29
    @41
    wceq
    @15
    @26
    @17
    a1i
    @2
    @30
    @25
    @14
    adantr
    @2
    @25
    simpr
    #
    @36
    @10
    cr
    vi
    cidp
    cF
    @6
    @36
    eqid
    @10
    eqid
    #
    coemul
    syl3anc
    @26
    @34
    @40
    @45
    vi
    @35
    @34
    wcel
    #
    @40
    @45
    wceq
    @26
    @49
    @40
    @42
    c1
    cc0
    cif
    #
    @39
    cmul
    co
    @45
    @49
    @37
    @50
    @39
    cmul
    @49
    @35
    cn0
    wcel
    @37
    @50
    wceq
    @35
    @6
    elfznn0
    @35
    coeidp
    syl
    oveq1d
    @42
    c1
    cc0
    @39
    cmul
    ovif
    syl6eq
    adantl
    sumeq2dv
    @26
    @46
    @34
    @35
    c1
    csn
    #
    wcel
    #
    @39
    cc0
    cif
    #
    vi
    csu
    #
    @12
    @26
    @34
    @45
    @53
    vi
    @26
    @49
    wa
    #
    @42
    @52
    @43
    @44
    @39
    cc0
    @42
    @52
    wb
    @55
    @52
    @42
    vi
    c1
    velsn
    #
    bicomi
    #
    a1i
    @55
    @39
    @55
    @39
    @55
    cn0
    cr
    @38
    @10
    @2
    cn0
    cr
    @10
    wf
    #
    @25
    @49
    @2
    @30
    @13
    @58
    @14
    0re
    @10
    cr
    cF
    @48
    coef2
    sylancl
    #
    ad2antrr
    @49
    @38
    cn0
    wcel
    @26
    @35
    cc0
    @6
    fznn0sub
    adantl
    ffvelrnd
    recnd
    #
    mulid2d
    @55
    @39
    @60
    mul02d
    ifbieq12d
    sumeq2dv
    @8
    @54
    cc0
    wceq
    #
    @54
    @11
    wceq
    #
    @54
    @12
    wceq
    @26
    cc0
    @11
    cc0
    @12
    @54
    eqeq2
    @11
    @12
    @54
    eqeq2
    @8
    @61
    @26
    @8
    @54
    cc0
    csn
    #
    cc0
    vi
    csu
    #
    cc0
    @8
    @34
    @63
    @53
    cc0
    vi
    @8
    @34
    cc0
    cc0
    cfz
    co
    #
    @63
    @6
    cc0
    cc0
    cfz
    oveq2
    cc0
    cz
    wcel
    @65
    @63
    wceq
    0z
    cc0
    fzsn
    ax-mp
    syl6eq
    @8
    @35
    @63
    wcel
    #
    wa
    #
    @42
    wn
    #
    @52
    wn
    #
    @53
    cc0
    wceq
    @67
    @35
    cc0
    wceq
    #
    @68
    @66
    @70
    @8
    @35
    cc0
    elsni
    adantl
    @70
    @42
    cc0
    c1
    wceq
    c1
    cc0
    ax-1ne0
    nesymi
    @35
    cc0
    c1
    eqeq1
    mtbiri
    syl
    @68
    @69
    @42
    @52
    @57
    notbii
    biimpi
    @52
    @39
    cc0
    iffalse
    3syl
    sumeq12rdv
    @63
    cc0
    cuz
    cfv
    #
    wss
    #
    @63
    cfn
    wcel
    #
    wo
    @64
    cc0
    wceq
    @73
    @72
    cc0
    snfi
    olci
    @63
    vi
    cc0
    sumz
    ax-mp
    syl6eq
    adantl
    @26
    @8
    wn
    #
    wa
    #
    @2
    @6
    cn
    wcel
    #
    @62
    @2
    @25
    @74
    simpll
    @75
    @25
    @6
    cc0
    wne
    @76
    @26
    @25
    @74
    @47
    adantr
    @75
    @6
    cc0
    @26
    @74
    simpr
    neqned
    @6
    elnnne0
    sylanbrc
    @2
    @76
    wa
    #
    @51
    @39
    vi
    csu
    #
    @54
    @11
    @77
    @51
    @34
    wss
    @39
    cc
    wcel
    #
    vi
    @51
    wral
    @34
    @71
    wss
    #
    @34
    cfn
    wcel
    #
    wo
    #
    @78
    @54
    wceq
    @77
    c1
    @34
    @77
    c1
    cn0
    wcel
    #
    @25
    c1
    @6
    cle
    wbr
    c1
    @34
    wcel
    @83
    @77
    1nn0
    a1i
    @77
    @6
    @2
    @76
    simpr
    #
    nnnn0d
    @77
    @6
    @84
    nnge1d
    c1
    @6
    elfz2nn0
    syl3anbrc
    snssd
    @77
    @79
    vi
    @51
    @77
    @52
    wa
    #
    @39
    @85
    cn0
    cr
    @38
    @10
    @2
    @58
    @76
    @52
    @59
    ad2antrr
    @85
    @38
    @9
    cn0
    @52
    @38
    @9
    wceq
    #
    @77
    @52
    @42
    @86
    @56
    @35
    c1
    @6
    cmin
    oveq2
    #
    sylbi
    adantl
    @76
    @9
    cn0
    wcel
    #
    @2
    @52
    @6
    nnm1nn0
    #
    ad2antlr
    eqeltrd
    ffvelrnd
    recnd
    ralrimiva
    @82
    @77
    @81
    @80
    cc0
    @6
    fzfi
    olci
    a1i
    @51
    @34
    @39
    vi
    cc0
    sumss2
    syl21anc
    @77
    @16
    @11
    cc
    wcel
    @78
    @11
    wceq
    1re
    @77
    @11
    @77
    cn0
    cr
    @9
    @10
    @2
    @58
    @76
    @59
    adantr
    @76
    @88
    @2
    @89
    adantl
    ffvelrnd
    recnd
    @39
    @11
    vi
    c1
    cr
    @42
    @38
    @9
    @10
    @87
    fveq2d
    sumsn
    sylancr
    eqtr3d
    syl2anc
    ifbothda
    eqtrd
    3eqtrd
    eqtrd
    mpteq2dva
    eqtrd
end
