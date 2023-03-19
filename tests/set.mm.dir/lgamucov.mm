include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wss.mm"
include "cnt.mm"
include "wcel.mm"
include "wrex.mm"
include "crp.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "a1i.mm"
include "ccld.mm"
include "difss.mm"
include "sszcld.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "cldopn.mm"
include "mp2b.mm"
include "cnfldtopn.mm"
include "mopni2.mm"
include "syl3anc.mm"
include "wa.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "eldifad.mm"
include "adantr.mm"
include "abscld.mm"
include "simprl.mm"
include "rpred.mm"
include "readdcld.mm"
include "2re.mm"
include "rerpdivcld.mm"
include "arch.mm"
include "syl.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cle.mm"
include "c1.mm"
include "cn0.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "rphalfcld.mm"
include "rpxrd.mm"
include "blopn.mm"
include "simplr.mm"
include "simp-4r.mm"
include "nnred.mm"
include "ad4antr.mm"
include "resubcld.mm"
include "rehalfcld.mm"
include "subcld.mm"
include "abs2difd.mm"
include "wceq.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "abssubd.mm"
include "eqtrd.mm"
include "simpr.mm"
include "eqbrtrrd.mm"
include "lelttrd.mm"
include "rphalflt.mm"
include "lttrd.mm"
include "ltsubadd2d.mm"
include "mpbid.mm"
include "2rp.mm"
include "rpdivcld.mm"
include "ltaddrpd.mm"
include "simpllr.mm"
include "ltled.mm"
include "nnrecred.mm"
include "nn0cnd.mm"
include "addcld.mm"
include "ad5antr.mm"
include "ad6antr.mm"
include "dmgmn0.mm"
include "absrpcld.mm"
include "rpaddcld.mm"
include "ltaddrp2d.mm"
include "nnrpd.mm"
include "ltrecd.mm"
include "2cnd.mm"
include "rpcnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "rpne0d.mm"
include "recdivd.mm"
include "breqtrd.mm"
include "cneg.mm"
include "wn.mm"
include "eldmgm.mm"
include "simprbi.mm"
include "negnegd.mm"
include "eqeltrd.mm"
include "nsyl3.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "negcld.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "subnegd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ltnled.mm"
include "3bitrd.mm"
include "elbl3.mm"
include "mpbird.mm"
include "blhalf.mm"
include "simprr.mm"
include "sstrd.mm"
include "sseld.mm"
include "sylbird.mm"
include "mt3d.mm"
include "ltletrd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ex.mm"
include "ss2rabdv.mm"
include "blval.mm"
include "3sstr4d.mm"
include "ssntr.mm"
include "blcntr.mm"
include "sseldd.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimddv.mm"

theorem lgamucov
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cU: class U
  let vk: setvar k
  let cJ: class J
  let vr: setvar r
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vz: setvar z
  let cG: class G
  assume lgamucov.u: |- U = { x e. CC | ( ( abs ` x ) <_ r /\ A. k e. NN0 ( 1 / r ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamucov.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )
  assume lgamucov.j: |- J = ( TopOpen ` CCfld )

  disjoint k r
  disjoint k x
  disjoint A k
  disjoint r x
  disjoint A r
  disjoint A x
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a t
  disjoint a x
  disjoint a z
  disjoint A a
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m x
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint r t
  disjoint r z
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint A z
  disjoint G n
  disjoint G r
  disjoint G z
  disjoint J a
  disjoint a ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph z
  disjoint U a
  disjoint U m
  disjoint U n
  disjoint U t
  disjoint U z
  assert |- ( ph -> E. r e. NN A e. ( ( int ` J ) ` U ) )

  proof
    wph
    cA
    va
    cv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    cc
    cz
    cn
    cdif
    #
    cdif
    #
    wss
    #
    cA
    cU
    cJ
    cnt
    cfv
    cfv
    #
    wcel
    #
    vr
    cn
    wrex
    #
    va
    crp
    wph
    @1
    cc
    cxmt
    cfv
    wcel
    #
    @5
    cJ
    wcel
    #
    cA
    @5
    wcel
    #
    @6
    va
    crp
    wrex
    @10
    wph
    cnxmet
    a1i
    @11
    wph
    @4
    cz
    wss
    @4
    cJ
    ccld
    cfv
    wcel
    @11
    cz
    cn
    difss
    @4
    cJ
    lgamucov.j
    sszcld
    @4
    cJ
    cc
    cc
    cJ
    cJ
    lgamucov.j
    cnfldtopon
    toponunii
    #
    cldopn
    mp2b
    a1i
    lgamucov.a
    va
    @5
    @1
    cA
    cJ
    cc
    cJ
    lgamucov.j
    cnfldtopn
    #
    mopni2
    syl3anc
    wph
    @0
    crp
    wcel
    #
    @6
    wa
    #
    wa
    #
    cA
    cabs
    cfv
    #
    @0
    caddc
    co
    #
    c2
    @0
    cdiv
    co
    #
    caddc
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    vr
    cn
    wrex
    #
    @9
    @17
    @21
    cr
    wcel
    #
    @24
    @17
    @19
    @20
    @17
    @18
    @0
    @17
    cA
    wph
    cA
    cc
    wcel
    #
    @16
    wph
    cA
    cc
    @4
    lgamucov.a
    eldifad
    adantr
    #
    abscld
    #
    @17
    @0
    wph
    @15
    @6
    simprl
    #
    rpred
    #
    readdcld
    #
    @17
    c2
    @0
    c2
    cr
    wcel
    @17
    2re
    a1i
    @29
    rerpdivcld
    #
    readdcld
    #
    @21
    vr
    arch
    syl
    @17
    @23
    @8
    vr
    cn
    @17
    @22
    cn
    wcel
    #
    wa
    #
    @23
    @8
    @35
    @23
    wa
    #
    cA
    @0
    c2
    cdiv
    co
    #
    @2
    co
    #
    @7
    cA
    @36
    cJ
    ctop
    wcel
    #
    cU
    cc
    wss
    #
    @38
    cJ
    wcel
    #
    @38
    cU
    wss
    @38
    @7
    wss
    @39
    @36
    cJ
    lgamucov.j
    cnfldtop
    a1i
    @40
    @36
    cU
    vx
    cv
    #
    cabs
    cfv
    #
    @22
    cle
    wbr
    #
    c1
    @22
    cdiv
    co
    #
    @42
    vk
    cv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    #
    vx
    cc
    crab
    #
    cc
    lgamucov.u
    @51
    vx
    cc
    ssrab2
    eqsstri
    a1i
    @36
    @10
    @26
    @37
    cxr
    wcel
    #
    @41
    @10
    @36
    cnxmet
    a1i
    #
    @17
    @26
    @34
    @23
    @27
    ad2antrr
    #
    @36
    @37
    @36
    @0
    @17
    @15
    @34
    @23
    @29
    ad2antrr
    #
    rphalfcld
    #
    rpxrd
    #
    @1
    cA
    @37
    cJ
    cc
    @14
    blopn
    syl3anc
    @36
    cA
    @42
    @1
    co
    #
    @37
    clt
    wbr
    #
    vx
    cc
    crab
    #
    @52
    @38
    cU
    @36
    @60
    @51
    vx
    cc
    @36
    @42
    cc
    wcel
    #
    wa
    #
    @60
    @51
    @63
    @60
    wa
    #
    @44
    @50
    @64
    @43
    @22
    @64
    @42
    @36
    @62
    @60
    simplr
    #
    abscld
    #
    @64
    @22
    @17
    @34
    @23
    @62
    @60
    simp-4r
    #
    nnred
    #
    @64
    @43
    @21
    @22
    @66
    @17
    @25
    @34
    @23
    @62
    @60
    @33
    ad4antr
    #
    @68
    @64
    @43
    @19
    @21
    @66
    @17
    @19
    cr
    wcel
    @34
    @23
    @62
    @60
    @31
    ad4antr
    #
    @69
    @64
    @43
    @18
    cmin
    co
    #
    @0
    clt
    wbr
    @43
    @19
    clt
    wbr
    @64
    @71
    @37
    @0
    @64
    @43
    @18
    @66
    @17
    @18
    cr
    wcel
    @34
    @23
    @62
    @60
    @28
    ad4antr
    #
    resubcld
    #
    @64
    @0
    @17
    @0
    cr
    wcel
    #
    @34
    @23
    @62
    @60
    @30
    ad4antr
    #
    rehalfcld
    #
    @75
    @64
    @71
    @42
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @37
    @73
    @64
    @77
    @64
    @42
    cA
    @65
    @36
    @26
    @62
    @60
    @55
    ad2antrr
    #
    subcld
    abscld
    @76
    @64
    @42
    cA
    @65
    @79
    abs2difd
    @64
    @59
    @78
    @37
    clt
    @64
    @59
    cA
    @42
    cmin
    co
    cabs
    cfv
    #
    @78
    @64
    @26
    @62
    @59
    @80
    wceq
    @79
    @65
    cA
    @42
    @1
    @1
    eqid
    #
    cnmetdval
    syl2anc
    @64
    cA
    @42
    @79
    @65
    abssubd
    eqtrd
    @63
    @60
    simpr
    eqbrtrrd
    lelttrd
    @64
    @15
    @37
    @0
    clt
    wbr
    @36
    @15
    @62
    @60
    @56
    ad2antrr
    #
    @0
    rphalflt
    syl
    lttrd
    @64
    @43
    @18
    @0
    @66
    @72
    @75
    ltsubadd2d
    mpbid
    @64
    @19
    @20
    @70
    @64
    c2
    @0
    c2
    crp
    wcel
    @64
    2rp
    a1i
    @82
    rpdivcld
    #
    ltaddrpd
    lttrd
    @35
    @23
    @62
    @60
    simpllr
    lttrd
    ltled
    @64
    @49
    vk
    cn0
    @64
    @46
    cn0
    wcel
    #
    wa
    #
    @45
    @48
    @85
    @22
    @64
    @34
    @84
    @67
    adantr
    #
    nnrecred
    #
    @85
    @47
    @85
    @42
    @46
    @36
    @62
    @60
    @84
    simpllr
    #
    @85
    @46
    @64
    @84
    simpr
    #
    nn0cnd
    #
    addcld
    abscld
    #
    @85
    @45
    @37
    @48
    @87
    @64
    @37
    cr
    wcel
    @84
    @76
    adantr
    #
    @91
    @85
    @45
    c1
    @20
    cdiv
    co
    #
    @37
    clt
    @85
    @20
    @22
    clt
    wbr
    @45
    @93
    clt
    wbr
    @85
    @20
    @21
    @22
    @17
    @20
    cr
    wcel
    @34
    @23
    @62
    @60
    @84
    @32
    ad5antr
    #
    @64
    @25
    @84
    @69
    adantr
    @64
    @22
    cr
    wcel
    @84
    @68
    adantr
    @85
    @20
    @19
    @94
    @85
    @18
    @0
    @85
    cA
    @64
    @26
    @84
    @79
    adantr
    #
    @85
    cA
    wph
    @12
    @16
    @34
    @23
    @62
    @60
    @84
    lgamucov.a
    ad6antr
    dmgmn0
    absrpcld
    @64
    @15
    @84
    @82
    adantr
    #
    rpaddcld
    ltaddrp2d
    @35
    @23
    @62
    @60
    @84
    simp-4r
    lttrd
    @85
    @20
    @22
    @64
    @20
    crp
    wcel
    @84
    @83
    adantr
    @85
    @22
    @86
    nnrpd
    ltrecd
    mpbid
    @85
    c2
    @0
    @85
    2cnd
    @85
    @0
    @96
    rpcnd
    c2
    cc0
    wne
    @85
    2ne0
    a1i
    @85
    @0
    @96
    rpne0d
    recdivd
    breqtrd
    @85
    @37
    @48
    cle
    wbr
    #
    @46
    cneg
    #
    @5
    wcel
    #
    @99
    @98
    cneg
    #
    cn0
    wcel
    #
    @85
    @99
    @98
    cc
    wcel
    #
    @101
    wn
    @98
    eldmgm
    simprbi
    @85
    @100
    @46
    cn0
    @85
    @46
    @90
    negnegd
    @89
    eqeltrd
    nsyl3
    @85
    @97
    wn
    #
    @98
    @42
    @37
    @2
    co
    #
    wcel
    #
    @99
    @85
    @105
    @42
    @98
    @1
    co
    #
    @37
    clt
    wbr
    #
    @48
    @37
    clt
    wbr
    @103
    @85
    @10
    @53
    @62
    @102
    @105
    @107
    wb
    @10
    @85
    cnxmet
    a1i
    #
    @36
    @53
    @62
    @60
    @84
    @58
    ad3antrrr
    #
    @88
    @85
    @46
    @90
    negcld
    #
    @98
    @1
    @42
    @37
    cc
    elbl2
    syl22anc
    @85
    @106
    @48
    @37
    clt
    @85
    @106
    @42
    @98
    cmin
    co
    #
    cabs
    cfv
    #
    @48
    @85
    @62
    @102
    @106
    @112
    wceq
    @88
    @110
    @42
    @98
    @1
    @81
    cnmetdval
    syl2anc
    @85
    @111
    @47
    cabs
    @85
    @42
    @46
    @88
    @90
    subnegd
    fveq2d
    eqtrd
    breq1d
    @85
    @48
    @37
    @91
    @92
    ltnled
    3bitrd
    @85
    @104
    @5
    @98
    @85
    @104
    @3
    @5
    @85
    @10
    @62
    @74
    cA
    @104
    wcel
    #
    @104
    @3
    wss
    @108
    @88
    @64
    @74
    @84
    @75
    adantr
    @85
    @113
    @60
    @63
    @60
    @84
    simplr
    @85
    @10
    @53
    @62
    @26
    @113
    @60
    wb
    @108
    @109
    @88
    @95
    cA
    @1
    @42
    @37
    cc
    elbl3
    syl22anc
    mpbird
    @0
    @1
    cc
    @42
    cA
    blhalf
    syl22anc
    @17
    @6
    @34
    @23
    @62
    @60
    @84
    wph
    @15
    @6
    simprr
    ad5antr
    sstrd
    sseld
    sylbird
    mt3d
    ltletrd
    ltled
    ralrimiva
    jca
    ex
    ss2rabdv
    @36
    @10
    @26
    @53
    @38
    @61
    wceq
    @54
    @55
    @58
    vx
    @1
    cA
    @37
    cc
    blval
    syl3anc
    cU
    @52
    wceq
    @36
    lgamucov.u
    a1i
    3sstr4d
    cU
    cJ
    @38
    cc
    @13
    ssntr
    syl22anc
    @36
    @10
    @26
    @37
    crp
    wcel
    cA
    @38
    wcel
    @54
    @55
    @57
    @1
    cA
    @37
    cc
    blcntr
    syl3anc
    sseldd
    ex
    reximdva
    mpd
    rexlimddv
end
