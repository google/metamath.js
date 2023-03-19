include "cn.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cc0.mm"
include "cfzo.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "cn0.mm"
include "clt.mm"
include "elfzonn0.mm"
include "ad2antrl.mm"
include "nnnn0.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "nn0mulcld.mm"
include "simpl1.mm"
include "elfzolt2.mm"
include "cr.mm"
include "wb.mm"
include "cz.mm"
include "elfzoelz.mm"
include "zred.mm"
include "nnre.mm"
include "3ad2ant1.mm"
include "nngt0.mm"
include "jca.mm"
include "ltmuldiv.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "cc.mm"
include "nncn.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "nndivdvds.mm"
include "biimp3a.mm"
include "nnzd.mm"
include "mulgcdr.mm"
include "simprr.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "sylanbrc.mm"
include "sylan2b.mm"
include "cle.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "eqbrtrrd.mm"
include "nnz.mm"
include "dvdsval2.mm"
include "mpbid.mm"
include "cfz.mm"
include "elfzofz.mm"
include "elfznn0.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "3syl.mm"
include "divge0.mm"
include "elnn0z.mm"
include "ltdiv1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "gcddiv.mm"
include "syl32anc.mm"
include "dividd.mm"
include "3eqtr3d.mm"
include "simplbi.mm"
include "anim12i.mm"
include "ad2antll.mm"
include "zcnd.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "divcan4d.mm"
include "impbid.mm"
include "sylan2.mm"
include "f1o2d.mm"

theorem hashgcdlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let cM: class M
  let cN: class N
  let vw: setvar w
  assume hashgcdlem.a: |- A = { y e. ( 0 ..^ ( M / N ) ) | ( y gcd ( M / N ) ) = 1 }
  assume hashgcdlem.b: |- B = { z e. ( 0 ..^ M ) | ( z gcd M ) = N }
  assume hashgcdlem.f: |- F = ( x e. A |-> ( x x. N ) )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint x z
  disjoint M z
  disjoint A x
  disjoint B x
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint w x
  disjoint w y
  disjoint M w
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint N w
  assert |- ( ( M e. NN /\ N e. NN /\ N || M ) -> F : A -1-1-onto-> B )

  proof
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cM
    cdvds
    wbr
    #
    w3a
    #
    vx
    vw
    cA
    cB
    vx
    cv
    #
    cN
    cmul
    co
    #
    vw
    cv
    #
    cN
    cdiv
    co
    #
    cF
    hashgcdlem.f
    @4
    cA
    wcel
    #
    @3
    @4
    cc0
    cM
    cN
    cdiv
    co
    #
    cfzo
    co
    #
    wcel
    #
    @4
    @9
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    @5
    cB
    wcel
    #
    vy
    cv
    #
    @9
    cgcd
    co
    #
    c1
    wceq
    #
    @13
    vy
    @4
    @10
    cA
    @16
    @4
    wceq
    @17
    @12
    c1
    @16
    @4
    @9
    cgcd
    oveq1
    eqeq1d
    hashgcdlem.a
    elrab2
    #
    @3
    @14
    wa
    #
    @5
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @5
    cM
    cgcd
    co
    #
    cN
    wceq
    #
    @15
    @20
    @5
    cn0
    wcel
    @0
    @5
    cM
    clt
    wbr
    #
    @22
    @20
    @4
    cN
    @11
    @4
    cn0
    wcel
    @3
    @13
    @4
    @9
    elfzonn0
    ad2antrl
    @3
    cN
    cn0
    wcel
    #
    @14
    @1
    @0
    @26
    @2
    cN
    nnnn0
    3ad2ant2
    adantr
    #
    nn0mulcld
    @0
    @1
    @2
    @14
    simpl1
    @20
    @25
    @4
    @9
    clt
    wbr
    #
    @11
    @28
    @3
    @13
    @4
    cc0
    @9
    elfzolt2
    ad2antrl
    @20
    @4
    cr
    wcel
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    wa
    #
    @25
    @28
    wb
    @20
    @4
    @11
    @4
    cz
    wcel
    #
    @3
    @13
    @4
    cc0
    @9
    elfzoelz
    #
    ad2antrl
    #
    zred
    @3
    @29
    @14
    @0
    @1
    @29
    @2
    cM
    nnre
    3ad2ant1
    #
    adantr
    @3
    @32
    @14
    @1
    @0
    @32
    @2
    @1
    @30
    @31
    cN
    nnre
    cN
    nngt0
    jca
    3ad2ant2
    #
    adantr
    @4
    cM
    cN
    ltmuldiv
    syl3anc
    mpbird
    @5
    cM
    elfzo0
    syl3anbrc
    @20
    @23
    @5
    @9
    cN
    cmul
    co
    #
    cgcd
    co
    #
    @12
    cN
    cmul
    co
    #
    cN
    @20
    cM
    @38
    @5
    cgcd
    @20
    @38
    cM
    @3
    @38
    cM
    wceq
    @14
    @3
    cM
    cN
    @0
    @1
    cM
    cc
    wcel
    @2
    cM
    nncn
    3ad2ant1
    @1
    @0
    cN
    cc
    wcel
    #
    @2
    cN
    nncn
    3ad2ant2
    #
    @1
    @0
    cN
    cc0
    wne
    #
    @2
    cN
    nnne0
    3ad2ant2
    #
    divcan1d
    adantr
    eqcomd
    oveq2d
    @20
    @33
    @9
    cz
    wcel
    #
    @26
    @39
    @40
    wceq
    @35
    @3
    @45
    @14
    @3
    @9
    @0
    @1
    @2
    @9
    cn
    wcel
    #
    cM
    cN
    nndivdvds
    biimp3a
    #
    nnzd
    adantr
    @27
    @4
    @9
    cN
    mulgcdr
    syl3anc
    @20
    @40
    c1
    cN
    cmul
    co
    #
    cN
    @20
    @12
    c1
    cN
    cmul
    @3
    @11
    @13
    simprr
    oveq1d
    @3
    @48
    cN
    wceq
    @14
    @3
    cN
    @42
    mulid2d
    adantr
    eqtrd
    3eqtrd
    vz
    cv
    #
    cM
    cgcd
    co
    #
    cN
    wceq
    #
    @24
    vz
    @5
    @21
    cB
    @49
    @5
    wceq
    @50
    @23
    cN
    @49
    @5
    cM
    cgcd
    oveq1
    eqeq1d
    hashgcdlem.b
    elrab2
    sylanbrc
    sylan2b
    @6
    cB
    wcel
    #
    @3
    @6
    @21
    wcel
    #
    @6
    cM
    cgcd
    co
    #
    cN
    wceq
    #
    wa
    #
    @7
    cA
    wcel
    #
    @51
    @55
    vz
    @6
    @21
    cB
    @49
    @6
    wceq
    @50
    @54
    cN
    @49
    @6
    cM
    cgcd
    oveq1
    eqeq1d
    hashgcdlem.b
    elrab2
    #
    @3
    @56
    wa
    #
    @7
    @10
    wcel
    #
    @7
    @9
    cgcd
    co
    #
    c1
    wceq
    #
    @57
    @59
    @7
    cn0
    wcel
    #
    @46
    @7
    @9
    clt
    wbr
    #
    @60
    @59
    @7
    cz
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @63
    @59
    cN
    @6
    cdvds
    wbr
    #
    @65
    @59
    @54
    cN
    @6
    cdvds
    @3
    @53
    @55
    simprr
    #
    @59
    @54
    @6
    cdvds
    wbr
    #
    @54
    cM
    cdvds
    wbr
    #
    @59
    @6
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @69
    @70
    wa
    @53
    @71
    @3
    @55
    @6
    cc0
    cM
    elfzoelz
    #
    ad2antrl
    #
    @59
    cM
    @0
    @1
    @2
    @56
    simpl1
    nnzd
    #
    @6
    cM
    gcddvds
    syl2anc
    simpld
    eqbrtrrd
    #
    @59
    cN
    cz
    wcel
    #
    @43
    @71
    @67
    @65
    wb
    @3
    @77
    @56
    @1
    @0
    @77
    @2
    cN
    nnz
    3ad2ant2
    adantr
    @3
    @43
    @56
    @44
    adantr
    @74
    cN
    @6
    dvdsval2
    syl3anc
    mpbid
    @59
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    wa
    #
    @32
    @66
    @59
    @6
    cc0
    cM
    cfz
    co
    wcel
    #
    @6
    cn0
    wcel
    #
    @80
    @53
    @81
    @3
    @55
    @6
    cc0
    cM
    elfzofz
    ad2antrl
    @6
    cM
    elfznn0
    @82
    @78
    @79
    @6
    nn0re
    @6
    nn0ge0
    jca
    3syl
    @3
    @32
    @56
    @37
    adantr
    #
    @6
    cN
    divge0
    syl2anc
    @7
    elnn0z
    sylanbrc
    @3
    @46
    @56
    @47
    adantr
    @59
    @6
    cM
    clt
    wbr
    #
    @64
    @53
    @84
    @3
    @55
    @6
    cc0
    cM
    elfzolt2
    ad2antrl
    @59
    @78
    @29
    @32
    @84
    @64
    wb
    @59
    @6
    @74
    zred
    @3
    @29
    @56
    @36
    adantr
    @83
    @6
    cM
    cN
    ltdiv1
    syl3anc
    mpbid
    @7
    @9
    elfzo0
    syl3anbrc
    @59
    @54
    cN
    cdiv
    co
    #
    cN
    cN
    cdiv
    co
    #
    @61
    c1
    @59
    @54
    cN
    cN
    cdiv
    @68
    oveq1d
    @59
    @71
    @72
    @1
    @67
    @2
    @85
    @61
    wceq
    @74
    @75
    @0
    @1
    @2
    @56
    simpl2
    @76
    @0
    @1
    @2
    @56
    simpl3
    @6
    cM
    cN
    gcddiv
    syl32anc
    @3
    @86
    c1
    wceq
    @56
    @3
    cN
    @42
    @44
    dividd
    adantr
    3eqtr3d
    @18
    @62
    vy
    @7
    @10
    cA
    @16
    @7
    wceq
    @17
    @61
    c1
    @16
    @7
    @9
    cgcd
    oveq1
    eqeq1d
    hashgcdlem.a
    elrab2
    sylanbrc
    sylan2b
    @8
    @52
    wa
    @3
    @11
    @53
    wa
    #
    @4
    @7
    wceq
    #
    @6
    @5
    wceq
    #
    wb
    @8
    @11
    @52
    @53
    @8
    @11
    @13
    @19
    simplbi
    @52
    @53
    @55
    @58
    simplbi
    anim12i
    @3
    @87
    wa
    #
    @88
    @89
    @90
    @89
    @88
    @6
    @7
    cN
    cmul
    co
    #
    wceq
    @90
    @91
    @6
    @90
    @6
    cN
    @90
    @6
    @53
    @71
    @3
    @11
    @73
    ad2antll
    zcnd
    @3
    @41
    @87
    @42
    adantr
    #
    @3
    @43
    @87
    @44
    adantr
    #
    divcan1d
    eqcomd
    @88
    @5
    @91
    @6
    @4
    @7
    cN
    cmul
    oveq1
    eqeq2d
    syl5ibrcom
    @90
    @88
    @89
    @4
    @5
    cN
    cdiv
    co
    #
    wceq
    @90
    @94
    @4
    @90
    @4
    cN
    @90
    @4
    @11
    @33
    @3
    @53
    @34
    ad2antrl
    zcnd
    @92
    @93
    divcan4d
    eqcomd
    @89
    @7
    @94
    @4
    @6
    @5
    cN
    cdiv
    oveq1
    eqeq2d
    syl5ibrcom
    impbid
    sylan2
    f1o2d
end
