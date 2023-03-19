include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "wa.mm"
include "clogb.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "nn0z.mm"
include "adantr.mm"
include "crp.mm"
include "wne.mm"
include "cr.mm"
include "2rp.mm"
include "a1i.mm"
include "elfzoelz.mm"
include "zred.mm"
include "adantl.mm"
include "cc0.mm"
include "cuz.mm"
include "w3a.mm"
include "wi.mm"
include "elfzo2.mm"
include "eluz2.mm"
include "2re.mm"
include "2pos.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "0red.mm"
include "zre.mm"
include "ad2antlr.mm"
include "ltletr.mm"
include "mpand.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "elrpd.mm"
include "1ne2.mm"
include "necomi.mm"
include "relogbcl.mm"
include "flcld.mm"
include "cmin.mm"
include "wb.mm"
include "eluzelz.mm"
include "zltlem1.mm"
include "sylan.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "eluzelre.mm"
include "3jca.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3exp.mm"
include "com34.mm"
include "3imp.mm"
include "imp.mm"
include "adantlr.mm"
include "peano2nn0.mm"
include "reexpcld.mm"
include "peano2rem.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "1lt2.mm"
include "expgt1.mm"
include "1red.mm"
include "posdifd.mm"
include "mpbid.mm"
include "logbleb.mm"
include "jca.mm"
include "relogbzcl.mm"
include "simpr.mm"
include "flwordi.mm"
include "logbpw2m1.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "sylibd.mm"
include "sylbid.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0red.mm"
include "flle.mm"
include "rpexpcld.mm"
include "leidd.mm"
include "nnlogbexp.mm"
include "breqtrrd.mm"
include "elfzole1.mm"
include "letrd.mm"
include "flflp1.mm"
include "zgeltp1eq.mm"
include "syl22anc.mm"
include "eqcomd.mm"

theorem fllog2
  let cI: class I
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( I e. NN0 /\ N e. ( ( 2 ^ I ) ..^ ( 2 ^ ( I + 1 ) ) ) ) -> ( |_ ` ( 2 logb N ) ) = I )

  proof
    cI
    cn0
    wcel
    #
    cN
    c2
    cI
    cexp
    co
    #
    c2
    cI
    c1
    caddc
    co
    #
    cexp
    co
    #
    cfzo
    co
    wcel
    #
    wa
    #
    cI
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    @5
    cI
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @7
    cI
    cle
    wbr
    #
    cI
    @7
    c1
    caddc
    co
    clt
    wbr
    #
    cI
    @7
    wceq
    #
    @0
    @8
    @4
    cI
    nn0z
    #
    adantr
    @5
    @6
    @5
    c2
    crp
    wcel
    #
    cN
    crp
    wcel
    #
    c2
    c1
    wne
    #
    @6
    cr
    wcel
    #
    @14
    @5
    2rp
    a1i
    @5
    cN
    @4
    cN
    cr
    wcel
    #
    @0
    @4
    cN
    cN
    @1
    @3
    elfzoelz
    zred
    adantl
    @4
    @0
    cc0
    cN
    clt
    wbr
    #
    @4
    cN
    @1
    cuz
    cfv
    wcel
    #
    @3
    cz
    wcel
    #
    cN
    @3
    clt
    wbr
    #
    w3a
    #
    @0
    @19
    wi
    #
    cN
    @1
    @3
    elfzo2
    #
    @20
    @21
    @24
    @22
    @20
    @1
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @1
    cN
    cle
    wbr
    #
    w3a
    #
    @24
    @1
    cN
    eluz2
    #
    @26
    @27
    @28
    @24
    @26
    @27
    wa
    #
    @0
    @28
    @19
    @31
    @0
    @28
    @19
    wi
    #
    @31
    @0
    wa
    #
    cc0
    @1
    clt
    wbr
    #
    @28
    @19
    @0
    @34
    @31
    @0
    c2
    cr
    wcel
    #
    @8
    cc0
    c2
    clt
    wbr
    #
    @34
    @35
    @0
    2re
    a1i
    #
    @13
    @36
    @0
    2pos
    a1i
    #
    c2
    cI
    expgt0
    #
    syl3anc
    adantl
    @33
    cc0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @18
    @34
    @28
    wa
    @19
    wi
    #
    @33
    0red
    @31
    @41
    @0
    @26
    @41
    @27
    @1
    zre
    #
    adantr
    adantr
    @27
    @18
    @26
    @0
    cN
    zre
    #
    ad2antlr
    cc0
    @1
    cN
    ltletr
    #
    syl3anc
    mpand
    ex
    com23
    3impia
    sylbi
    3ad2ant1
    sylbi
    impcom
    elrpd
    #
    @16
    @5
    c1
    c2
    1ne2
    necomi
    #
    a1i
    c2
    cN
    relogbcl
    #
    syl3anc
    #
    flcld
    @4
    @0
    @10
    @4
    @23
    @0
    @10
    wi
    #
    @25
    @20
    @21
    @22
    @50
    @20
    @21
    wa
    #
    @22
    cN
    @3
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @50
    @20
    @27
    @21
    @22
    @53
    wb
    @1
    cN
    eluzelz
    cN
    @3
    zltlem1
    sylan
    @51
    @0
    @53
    @10
    @51
    @0
    @53
    @10
    wi
    @51
    @0
    wa
    #
    @53
    @6
    c2
    @52
    clogb
    co
    #
    cle
    wbr
    #
    @10
    @54
    c2
    c2
    cuz
    cfv
    wcel
    #
    @15
    @52
    crp
    wcel
    #
    @53
    @56
    wb
    @57
    @54
    c2
    cz
    wcel
    @57
    2z
    c2
    uzid
    ax-mp
    #
    a1i
    @20
    @0
    @15
    @21
    @20
    @0
    wa
    cN
    @20
    @18
    @0
    @1
    cN
    eluzelre
    #
    adantr
    @20
    @0
    @19
    @20
    @29
    @24
    @30
    @26
    @27
    @28
    @24
    @26
    @27
    @0
    @28
    @19
    @26
    @27
    @0
    @32
    @26
    @27
    @0
    w3a
    #
    @34
    @28
    @19
    @61
    @35
    @8
    @36
    w3a
    #
    @34
    @0
    @26
    @62
    @27
    @0
    @35
    @8
    @36
    @37
    @13
    @38
    3jca
    3ad2ant3
    @39
    syl
    @61
    @40
    @41
    @18
    @42
    @61
    0red
    @26
    @27
    @41
    @0
    @43
    3ad2ant1
    @27
    @26
    @18
    @0
    @44
    3ad2ant2
    @45
    syl3anc
    mpand
    3exp
    com34
    3imp
    sylbi
    imp
    #
    elrpd
    adantlr
    @54
    @52
    @54
    @3
    cr
    wcel
    #
    @52
    cr
    wcel
    #
    @54
    c2
    @2
    @35
    @54
    2re
    a1i
    @0
    @2
    cn0
    wcel
    @51
    cI
    peano2nn0
    #
    adantl
    reexpcld
    @3
    peano2rem
    #
    syl
    @54
    c1
    @3
    clt
    wbr
    #
    cc0
    @52
    clt
    wbr
    #
    @54
    @35
    @2
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    w3a
    #
    @68
    @0
    @72
    @51
    @0
    @35
    @70
    @71
    @37
    cI
    nn0p1nn
    #
    @71
    @0
    1lt2
    a1i
    #
    3jca
    adantl
    c2
    @2
    expgt1
    #
    syl
    @54
    c1
    @3
    @54
    1red
    @21
    @64
    @20
    @0
    @3
    zre
    ad2antlr
    posdifd
    mpbid
    elrpd
    c2
    cN
    @52
    logbleb
    syl3anc
    @54
    @56
    @7
    @55
    cfl
    cfv
    #
    cle
    wbr
    #
    @10
    @54
    @56
    @77
    @54
    @56
    wa
    @17
    @55
    cr
    wcel
    #
    @56
    @77
    @54
    @17
    @56
    @54
    @14
    @15
    @16
    @17
    @14
    @54
    2rp
    a1i
    @54
    cN
    @51
    @18
    @0
    @20
    @18
    @21
    @60
    adantr
    adantr
    @20
    @0
    @19
    @21
    @63
    adantlr
    elrpd
    @16
    @54
    @47
    a1i
    @48
    syl3anc
    adantr
    @54
    @78
    @56
    @54
    @57
    @58
    wa
    #
    @78
    @0
    @79
    @51
    @0
    @57
    @58
    @57
    @0
    @59
    a1i
    #
    @0
    @52
    @0
    @64
    @65
    @0
    c2
    @2
    @37
    @66
    reexpcld
    #
    @67
    syl
    @0
    @68
    @69
    @0
    @35
    @70
    @71
    @68
    @37
    @73
    @74
    @75
    syl3anc
    @0
    c1
    @3
    @0
    1red
    @81
    posdifd
    mpbid
    elrpd
    jca
    adantl
    c2
    @52
    relogbzcl
    syl
    adantr
    @54
    @56
    simpr
    @6
    @55
    flwordi
    syl3anc
    ex
    @54
    @76
    cI
    @7
    cle
    @54
    @76
    @2
    c1
    cmin
    co
    #
    cI
    @54
    @70
    @76
    @82
    wceq
    @0
    @70
    @51
    @73
    adantl
    @2
    logbpw2m1
    syl
    @0
    @82
    cI
    wceq
    #
    @51
    @0
    cI
    cc
    wcel
    @83
    cI
    nn0cn
    cI
    pncan1
    syl
    adantl
    eqtrd
    breq2d
    sylibd
    sylbid
    ex
    com23
    sylbid
    3impia
    sylbi
    impcom
    @5
    cI
    cfl
    cfv
    #
    @6
    cle
    wbr
    #
    @11
    @5
    @84
    cI
    @6
    @0
    @84
    cr
    wcel
    @4
    @0
    @84
    @0
    cI
    cr
    wcel
    #
    cc0
    cI
    cle
    wbr
    @84
    cn0
    wcel
    cI
    nn0re
    #
    cI
    nn0ge0
    cI
    flge0nn0
    syl2anc
    nn0red
    adantr
    @0
    @86
    @4
    @87
    adantr
    #
    @49
    @0
    @84
    cI
    cle
    wbr
    #
    @4
    @0
    @86
    @89
    @87
    cI
    flle
    syl
    adantr
    @5
    cI
    c2
    @1
    clogb
    co
    #
    @6
    @88
    @0
    @90
    cr
    wcel
    #
    @4
    @0
    @14
    @1
    crp
    wcel
    #
    @16
    @91
    @14
    @0
    2rp
    a1i
    #
    @0
    c2
    cI
    @93
    @13
    rpexpcld
    #
    @16
    @0
    @47
    a1i
    c2
    @1
    relogbcl
    syl3anc
    adantr
    @49
    @0
    cI
    @90
    cle
    wbr
    @4
    @0
    cI
    cI
    @90
    cle
    @0
    cI
    @87
    leidd
    @0
    @57
    @8
    @90
    cI
    wceq
    @80
    @13
    c2
    cI
    nnlogbexp
    syl2anc
    breqtrrd
    adantr
    @5
    @28
    @90
    @6
    cle
    wbr
    #
    @4
    @28
    @0
    cN
    @1
    @3
    elfzole1
    adantl
    @5
    @57
    @92
    @15
    @28
    @95
    wb
    @57
    @5
    @59
    a1i
    @0
    @92
    @4
    @94
    adantr
    @46
    c2
    @1
    cN
    logbleb
    syl3anc
    mpbid
    letrd
    letrd
    @5
    @86
    @17
    @85
    @11
    wb
    @88
    @49
    cI
    @6
    flflp1
    syl2anc
    mpbid
    @8
    @9
    wa
    @10
    @11
    wa
    @12
    @7
    cI
    zgeltp1eq
    imp
    syl22anc
    eqcomd
end
