include "cfv.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cxr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wcel.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "adantrl.mm"
include "rexlimiva.mm"
include "abssi.mm"
include "cc0.mm"
include "c0v.mm"
include "ax-hv0cl.mm"
include "norm0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "eqcomi.mm"
include "pm3.2i.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "c0ex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "mpbir.mm"
include "ne0ii.mm"
include "wi.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wal.mm"
include "2rp.mm"
include "rpdivcl.mm"
include "mpan.mm"
include "rpred.mm"
include "adantr.mm"
include "csm.mm"
include "cc.mm"
include "rpre.mm"
include "rehalfcld.mm"
include "recnd.mm"
include "simprl.mm"
include "hvmulcl.mm"
include "syl2anc.mm"
include "normcl.mm"
include "syl.mm"
include "cmul.mm"
include "simprr.mm"
include "ad2antrl.mm"
include "1red.mm"
include "rphalfcl.mm"
include "lemul2d.mm"
include "mpbid.mm"
include "cabs.mm"
include "rpcn.mm"
include "norm-iii.mm"
include "sylan.mm"
include "rpge0.mm"
include "absidd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "mulid1d.mm"
include "3brtr3d.mm"
include "rphalflt.mm"
include "lelttrd.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "ltmuldiv2d.mm"
include "rprecred.mm"
include "ltle.mm"
include "sylbid.mm"
include "rpne0.mm"
include "2cn.mm"
include "2ne0.mm"
include "recdiv.mm"
include "mpanr12.mm"
include "breq2d.mm"
include "3imtr3d.mm"
include "syld.mm"
include "an32s.mm"
include "anassrs.mm"
include "breq1.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "alrimiv.mm"
include "ralab.mm"
include "breq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "syl5bb.mm"
include "ax-mp.mm"
include "supxrre.mm"
include "mp3an.mm"
include "eqtri.mm"
include "suprcl.mm"
include "eqeltri.mm"

theorem nmcexi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cT: class T
  let vm: setvar m
  let cN: class N
  let vn: setvar n
  assume nmcex.1: |- E. y e. RR+ A. z e. ~H ( ( normh ` z ) < y -> ( N ` ( T ` z ) ) < 1 )
  assume nmcex.2: |- ( S ` T ) = sup ( { m | E. x e. ~H ( ( normh ` x ) <_ 1 /\ m = ( N ` ( T ` x ) ) ) } , RR* , < )
  assume nmcex.3: |- ( x e. ~H -> ( N ` ( T ` x ) ) e. RR )
  assume nmcex.4: |- ( N ` ( T ` 0h ) ) = 0
  assume nmcex.5: |- ( ( ( y / 2 ) e. RR+ /\ x e. ~H ) -> ( ( y / 2 ) x. ( N ` ( T ` x ) ) ) = ( N ` ( T ` ( ( y / 2 ) .h x ) ) ) )

  disjoint m x
  disjoint m y
  disjoint m z
  disjoint N m
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint T m
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint m n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint T n
  assert |- ( S ` T ) e. RR

  proof
    cT
    cS
    cfv
    #
    vx
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vm
    cv
    #
    @1
    cT
    cfv
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    #
    vm
    cab
    #
    cr
    clt
    csup
    #
    cr
    @0
    @10
    cxr
    clt
    csup
    #
    @11
    nmcex.2
    @10
    cr
    wss
    #
    @10
    c0
    wne
    #
    vn
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vn
    @10
    wral
    #
    vz
    cr
    wrex
    #
    @12
    @11
    wceq
    @9
    vm
    cr
    @8
    @4
    cr
    wcel
    #
    vx
    chil
    @1
    chil
    wcel
    #
    @7
    @20
    @3
    @21
    @7
    @20
    @21
    @20
    @7
    @6
    cr
    wcel
    #
    nmcex.3
    @4
    @6
    cr
    eleq1
    syl5ibrcom
    imp
    adantrl
    rexlimiva
    abssi
    #
    cc0
    @10
    cc0
    @10
    wcel
    @3
    cc0
    @6
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    #
    c0v
    chil
    wcel
    c0v
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    cc0
    c0v
    cT
    cfv
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    @26
    ax-hv0cl
    @28
    @31
    @27
    cc0
    c1
    cle
    norm0
    0le1
    eqbrtri
    @30
    cc0
    nmcex.4
    eqcomi
    pm3.2i
    @25
    @32
    vx
    c0v
    chil
    @1
    c0v
    wceq
    #
    @3
    @28
    @24
    @31
    @33
    @2
    @27
    c1
    cle
    @1
    c0v
    cno
    fveq2
    breq1d
    @33
    @6
    @30
    cc0
    @33
    @5
    @29
    cN
    @1
    c0v
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    mp2an
    @9
    @26
    vm
    cc0
    c0ex
    @4
    cc0
    wceq
    #
    @8
    @25
    vx
    chil
    @34
    @7
    @24
    @3
    @4
    cc0
    @6
    eqeq1
    anbi2d
    rexbidv
    elab
    mpbir
    ne0ii
    #
    @16
    cno
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @16
    cT
    cfv
    #
    cN
    cfv
    #
    c1
    clt
    wbr
    #
    wi
    #
    vz
    chil
    wral
    #
    vy
    crp
    wrex
    @19
    nmcex.1
    @43
    @19
    vy
    crp
    @37
    crp
    wcel
    #
    @43
    wa
    #
    c2
    @37
    cdiv
    co
    #
    cr
    wcel
    #
    @3
    @15
    @6
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    #
    @15
    @46
    cle
    wbr
    #
    wi
    #
    vn
    wal
    #
    @19
    @44
    @47
    @43
    @44
    @46
    c2
    crp
    wcel
    @44
    @46
    crp
    wcel
    2rp
    c2
    @37
    rpdivcl
    mpan
    rpred
    adantr
    @45
    @52
    vn
    @45
    @49
    @51
    vx
    chil
    @45
    @21
    wa
    #
    @3
    @48
    @51
    @54
    @3
    wa
    @51
    @48
    @6
    @46
    cle
    wbr
    #
    @45
    @21
    @3
    @55
    @44
    @21
    @3
    wa
    #
    @43
    @55
    @44
    @56
    wa
    #
    @43
    @55
    @57
    @43
    @37
    c2
    cdiv
    co
    #
    @1
    csm
    co
    #
    cT
    cfv
    #
    cN
    cfv
    #
    c1
    clt
    wbr
    #
    @55
    @57
    @43
    @59
    cno
    cfv
    #
    @37
    clt
    wbr
    #
    @62
    @57
    @63
    @58
    @37
    @57
    @59
    chil
    wcel
    #
    @63
    cr
    wcel
    @57
    @58
    cc
    wcel
    #
    @21
    @65
    @57
    @58
    @57
    @37
    @44
    @37
    cr
    wcel
    @56
    @37
    rpre
    adantr
    #
    rehalfcld
    #
    recnd
    #
    @44
    @21
    @3
    simprl
    #
    @58
    @1
    hvmulcl
    syl2anc
    #
    @59
    normcl
    syl
    @68
    @67
    @57
    @58
    @2
    cmul
    co
    #
    @58
    c1
    cmul
    co
    #
    @63
    @58
    cle
    @57
    @3
    @72
    @73
    cle
    wbr
    @44
    @21
    @3
    simprr
    @57
    @2
    c1
    @58
    @21
    @2
    cr
    wcel
    @44
    @3
    @1
    normcl
    ad2antrl
    @57
    1red
    #
    @44
    @58
    crp
    wcel
    #
    @56
    @37
    rphalfcl
    adantr
    #
    lemul2d
    mpbid
    @57
    @75
    @21
    @72
    @63
    wceq
    @76
    @70
    @75
    @21
    wa
    @63
    @58
    cabs
    cfv
    #
    @2
    cmul
    co
    #
    @72
    @75
    @66
    @21
    @63
    @78
    wceq
    @58
    rpcn
    @58
    @1
    norm-iii
    sylan
    @75
    @78
    @72
    wceq
    @21
    @75
    @77
    @58
    @2
    cmul
    @75
    @58
    @58
    rpre
    @58
    rpge0
    absidd
    oveq1d
    adantr
    eqtr2d
    syl2anc
    @57
    @58
    @69
    mulid1d
    3brtr3d
    @44
    @58
    @37
    clt
    wbr
    @56
    @37
    rphalflt
    adantr
    lelttrd
    @57
    @65
    @43
    @64
    @62
    wi
    #
    wi
    @71
    @42
    @79
    vz
    @59
    chil
    @16
    @59
    wceq
    #
    @38
    @64
    @41
    @62
    @80
    @36
    @63
    @37
    clt
    @16
    @59
    cno
    fveq2
    breq1d
    @80
    @40
    @61
    c1
    clt
    @80
    @39
    @60
    cN
    @16
    @59
    cT
    fveq2
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl
    mpid
    @57
    @58
    @6
    cmul
    co
    #
    c1
    clt
    wbr
    #
    @6
    c1
    @58
    cdiv
    co
    #
    cle
    wbr
    #
    @62
    @55
    @57
    @82
    @6
    @83
    clt
    wbr
    #
    @84
    @57
    @6
    c1
    @58
    @21
    @22
    @44
    @3
    nmcex.3
    ad2antrl
    #
    @74
    @76
    ltmuldiv2d
    @57
    @22
    @83
    cr
    wcel
    @85
    @84
    wi
    @86
    @57
    @58
    @76
    rprecred
    @6
    @83
    ltle
    syl2anc
    sylbid
    @57
    @81
    @61
    c1
    clt
    @57
    @75
    @21
    @81
    @61
    wceq
    @76
    @70
    nmcex.5
    syl2anc
    breq1d
    @57
    @83
    @46
    @6
    cle
    @44
    @83
    @46
    wceq
    #
    @56
    @44
    @37
    cc
    wcel
    #
    @37
    cc0
    wne
    #
    @87
    @37
    rpcn
    @37
    rpne0
    @88
    @89
    wa
    c2
    cc
    wcel
    c2
    cc0
    wne
    @87
    2cn
    2ne0
    @37
    c2
    recdiv
    mpanr12
    syl2anc
    adantr
    breq2d
    3imtr3d
    syld
    imp
    an32s
    anassrs
    @15
    @6
    @46
    cle
    breq1
    syl5ibrcom
    expimpd
    rexlimdva
    alrimiv
    @18
    @53
    vz
    @46
    cr
    @18
    @50
    @17
    wi
    #
    vn
    wal
    @16
    @46
    wceq
    #
    @53
    @9
    @50
    @17
    vn
    vm
    @4
    @15
    wceq
    #
    @8
    @49
    vx
    chil
    @92
    @7
    @48
    @3
    @4
    @15
    @6
    eqeq1
    anbi2d
    rexbidv
    ralab
    @91
    @90
    @52
    vn
    @91
    @17
    @51
    @50
    @16
    @46
    @15
    cle
    breq2
    imbi2d
    albidv
    syl5bb
    rspcev
    syl2anc
    rexlimiva
    ax-mp
    #
    vz
    vn
    @10
    supxrre
    mp3an
    eqtri
    @13
    @14
    @19
    @11
    cr
    wcel
    @23
    @35
    @93
    vz
    vn
    @10
    suprcl
    mp3an
    eqeltri
end
