include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "crn.mm"
include "cmin.mm"
include "caddc.mm"
include "cioo.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "cz.mm"
include "cxp.mm"
include "wfn.mm"
include "cdiv.mm"
include "c1.mm"
include "cico.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "simpl.mm"
include "2rp.mm"
include "clogb.mm"
include "1red.mm"
include "cuz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "relogbzcl.mm"
include "mpan.mm"
include "resubcld.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "rpexpcl.mm"
include "rpred.mm"
include "sylancr.mm"
include "adantl.mm"
include "remulcld.mm"
include "fnovrn.mm"
include "syl3anc.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "zred.mm"
include "fllelt.mm"
include "syl.mm"
include "simpld.mm"
include "lediv1dd.mm"
include "recnd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "expne0d.mm"
include "divcan4d.mm"
include "breqtrd.mm"
include "readdcld.mm"
include "simprd.mm"
include "ltdiv1dd.mm"
include "eqbrtrrd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "redivcld.mm"
include "rexrd.mm"
include "elico2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "wceq.mm"
include "dya2iocival.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "rereccld.mm"
include "oveq2i.mm"
include "dya2ub.mm"
include "syl5eqbr.mm"
include "ltsub2dd.mm"
include "mulcld.mm"
include "1cnd.mm"
include "divsubdird.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "ltsub1dd.mm"
include "pncand.mm"
include "ltled.mm"
include "ltletrd.mm"
include "leadd1dd.mm"
include "divdird.mm"
include "ltadd2dd.mm"
include "lelttrd.mm"
include "icossioo.mm"
include "syl22anc.mm"
include "eqsstrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem dya2icoseg
  let vx: setvar x
  let cD: class D
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let vb: setvar b
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2icoseg.1: |- N = ( |_ ` ( 1 - ( 2 logb D ) ) )

  disjoint n x
  disjoint D b
  disjoint I b
  disjoint b x
  disjoint N b
  disjoint N x
  disjoint X b
  disjoint X x
  disjoint n x
  disjoint I x
  assert |- ( ( X e. RR /\ D e. RR+ ) -> E. b e. ran I ( X e. b /\ b C_ ( ( X - D ) (,) ( X + D ) ) ) )

  proof
    cX
    cr
    wcel
    #
    cD
    crp
    wcel
    #
    wa
    #
    cX
    c2
    cN
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    cN
    cI
    co
    #
    cI
    crn
    #
    wcel
    #
    cX
    @6
    wcel
    #
    @6
    cX
    cD
    cmin
    co
    #
    cX
    cD
    caddc
    co
    #
    cioo
    co
    #
    wss
    #
    cX
    vb
    cv
    #
    wcel
    #
    @14
    @12
    wss
    #
    wa
    #
    vb
    @7
    wrex
    @2
    cI
    cz
    cz
    cxp
    wfn
    #
    @5
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @8
    @18
    @2
    vx
    vn
    cz
    cz
    vx
    cv
    #
    c2
    vn
    cv
    cexp
    co
    #
    cdiv
    co
    #
    @21
    c1
    caddc
    co
    @22
    cdiv
    co
    #
    cico
    co
    cI
    dya2ioc.1
    @23
    @24
    cico
    ovex
    fnmpt2i
    a1i
    @2
    @4
    @2
    cX
    @3
    @0
    @1
    simpl
    #
    @1
    @3
    cr
    wcel
    #
    @0
    @1
    c2
    crp
    wcel
    #
    @20
    @26
    2rp
    @1
    cN
    c1
    c2
    cD
    clogb
    co
    #
    cmin
    co
    #
    cfl
    cfv
    #
    cz
    dya2icoseg.1
    @1
    @29
    @1
    c1
    @28
    @1
    1red
    c2
    c2
    cuz
    cfv
    wcel
    #
    @1
    @28
    cr
    wcel
    c2
    cz
    wcel
    @31
    2z
    c2
    uzid
    ax-mp
    c2
    cD
    relogbzcl
    mpan
    resubcld
    flcld
    syl5eqel
    #
    @27
    @20
    wa
    @3
    c2
    cN
    rpexpcl
    #
    rpred
    sylancr
    adantl
    #
    remulcld
    #
    flcld
    #
    @1
    @20
    @0
    @32
    adantl
    #
    cz
    cz
    @5
    cN
    cI
    fnovrn
    syl3anc
    @2
    cX
    @5
    @3
    cdiv
    co
    #
    @5
    c1
    caddc
    co
    #
    @3
    cdiv
    co
    #
    cico
    co
    #
    @6
    @2
    cX
    @41
    wcel
    #
    @0
    @38
    cX
    cle
    wbr
    #
    cX
    @40
    clt
    wbr
    #
    @25
    @2
    @38
    @4
    @3
    cdiv
    co
    #
    cX
    cle
    @2
    @5
    @4
    @3
    @2
    @5
    @36
    zred
    #
    @35
    @2
    @27
    @20
    @3
    crp
    wcel
    2rp
    @37
    @33
    sylancr
    #
    @2
    @5
    @4
    cle
    wbr
    #
    @4
    @39
    clt
    wbr
    #
    @2
    @4
    cr
    wcel
    @48
    @49
    wa
    @35
    @4
    fllelt
    syl
    #
    simpld
    #
    lediv1dd
    @2
    cX
    @3
    @2
    cX
    @25
    recnd
    #
    @2
    @3
    @34
    recnd
    #
    @2
    c2
    cN
    @2
    2cnd
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    @37
    expne0d
    #
    divcan4d
    #
    breqtrd
    @2
    @45
    cX
    @40
    clt
    @55
    @2
    @4
    @39
    @3
    @35
    @2
    @5
    c1
    @46
    @2
    1red
    #
    readdcld
    #
    @47
    @2
    @48
    @49
    @50
    simprd
    #
    ltdiv1dd
    eqbrtrrd
    @2
    @38
    cr
    wcel
    @40
    cxr
    wcel
    @42
    @0
    @43
    @44
    w3a
    wb
    @2
    @5
    @3
    @46
    @34
    @54
    redivcld
    #
    @2
    @40
    @2
    @39
    @3
    @57
    @34
    @54
    redivcld
    #
    rexrd
    @38
    @40
    cX
    elico2
    syl2anc
    mpbir3and
    @2
    @20
    @19
    @6
    @41
    wceq
    @37
    @36
    vx
    vn
    cI
    cJ
    cN
    @5
    sxbrsiga.0
    dya2ioc.1
    dya2iocival
    syl2anc
    #
    eleqtrrd
    @2
    @6
    @41
    @12
    @61
    @2
    @10
    cxr
    wcel
    @11
    cxr
    wcel
    @10
    @38
    clt
    wbr
    @40
    @11
    cle
    wbr
    @41
    @12
    wss
    @2
    @10
    @2
    cX
    cD
    @25
    @2
    cD
    @0
    @1
    simpr
    rpred
    #
    resubcld
    #
    rexrd
    @2
    @11
    @2
    cX
    cD
    @25
    @62
    readdcld
    #
    rexrd
    @2
    @10
    cX
    c1
    @3
    cdiv
    co
    #
    cmin
    co
    #
    @38
    @63
    @2
    cX
    @65
    @25
    @2
    @3
    @34
    @54
    rereccld
    #
    resubcld
    @59
    @2
    @65
    cD
    cX
    @67
    @62
    @25
    @2
    @65
    c1
    c2
    @30
    cexp
    co
    #
    cdiv
    co
    #
    cD
    clt
    @3
    @68
    c1
    cdiv
    cN
    @30
    c2
    cexp
    dya2icoseg.1
    oveq2i
    oveq2i
    @1
    @69
    cD
    clt
    wbr
    @0
    cD
    dya2ub
    adantl
    syl5eqbr
    #
    ltsub2dd
    @2
    @4
    c1
    cmin
    co
    #
    @3
    cdiv
    co
    #
    @66
    @38
    cle
    @2
    @72
    @45
    @65
    cmin
    co
    @66
    @2
    @4
    c1
    @3
    @2
    cX
    @3
    @52
    @53
    mulcld
    #
    @2
    1cnd
    #
    @53
    @54
    divsubdird
    @2
    @45
    cX
    @65
    cmin
    @55
    oveq1d
    eqtrd
    @2
    @71
    @5
    @3
    @2
    @4
    c1
    @35
    @56
    resubcld
    #
    @46
    @47
    @2
    @71
    @5
    @75
    @46
    @2
    @71
    @39
    c1
    cmin
    co
    @5
    clt
    @2
    @4
    @39
    c1
    @35
    @57
    @56
    @58
    ltsub1dd
    @2
    @5
    c1
    @2
    @5
    @46
    recnd
    @74
    pncand
    breqtrd
    ltled
    lediv1dd
    eqbrtrrd
    ltletrd
    @2
    @40
    @11
    @60
    @64
    @2
    @40
    cX
    @65
    caddc
    co
    #
    @11
    @60
    @2
    cX
    @65
    @25
    @67
    readdcld
    @64
    @2
    @40
    @4
    c1
    caddc
    co
    #
    @3
    cdiv
    co
    #
    @76
    cle
    @2
    @39
    @77
    @3
    @57
    @2
    @4
    c1
    @35
    @56
    readdcld
    @47
    @2
    @5
    @4
    c1
    @46
    @35
    @56
    @51
    leadd1dd
    lediv1dd
    @2
    @78
    @45
    @65
    caddc
    co
    @76
    @2
    @4
    c1
    @3
    @73
    @74
    @53
    @54
    divdird
    @2
    @45
    cX
    @65
    caddc
    @55
    oveq1d
    eqtrd
    breqtrd
    @2
    @65
    cD
    cX
    @67
    @62
    @25
    @70
    ltadd2dd
    lelttrd
    ltled
    @10
    @11
    @38
    @40
    icossioo
    syl22anc
    eqsstrd
    @17
    @9
    @13
    wa
    vb
    @6
    @7
    @14
    @6
    wceq
    @15
    @9
    @16
    @13
    @14
    @6
    cX
    eleq2
    @14
    @6
    @12
    sseq1
    anbi12d
    rspcev
    syl12anc
end
