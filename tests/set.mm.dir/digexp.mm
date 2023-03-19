include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmo.mm"
include "cmin.mm"
include "cdig.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "eluzelcn.mm"
include "eluz2nn.mm"
include "nnne0d.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "nn0z.mm"
include "anim12i.mm"
include "ancomd.mm"
include "3adant1.mm"
include "expsub.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cn.mm"
include "cpnf.mm"
include "cico.mm"
include "simp2.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelre.mm"
include "reexpcl.mm"
include "sylan.mm"
include "adantr.mm"
include "simpr.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "expge0d.mm"
include "3adant2.mm"
include "elrege0.mm"
include "sylibr.mm"
include "nn0digval.mm"
include "syl3anc.mm"
include "wb.mm"
include "nn0cn.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "subeq0ad.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "1zzd.mm"
include "flid.mm"
include "syl.mm"
include "clt.mm"
include "eluz2gt1.mm"
include "1mod.mm"
include "eqtr2d.mm"
include "wn.mm"
include "simprl1.mm"
include "adantl.mm"
include "zsubcld.mm"
include "ad2antrl.mm"
include "wi.mm"
include "nn0re.mm"
include "sublt0d.mm"
include "biimprd.mm"
include "impcom.mm"
include "expnegico01.mm"
include "ico01fl0.mm"
include "crp.mm"
include "nnrpd.mm"
include "0mod.mm"
include "eluzelz.mm"
include "lenlt.mm"
include "bicomd.mm"
include "biimpd.mm"
include "3simpc.mm"
include "nn0sub.mm"
include "mpbid.mm"
include "zexpcl.mm"
include "expm1d.mm"
include "wo.mm"
include "pm4.56.mm"
include "axlttri.mm"
include "syl5bi.mm"
include "expdimp.mm"
include "znnsub.mm"
include "nnm1nn0.mm"
include "eqeltrd.mm"
include "reexpclzd.mm"
include "mod0.mm"
include "pm2.61ian.mm"
include "ifeqda.mm"
include "3eqtr4d.mm"

theorem digexp
  let cB: class B
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ K e. NN0 /\ N e. NN0 ) -> ( K ( digit ` B ) ( B ^ N ) ) = if ( K = N , 1 , 0 ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cK
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cB
    cN
    cexp
    co
    #
    cB
    cK
    cexp
    co
    cdiv
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    cB
    cN
    cK
    cmin
    co
    #
    cexp
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    cK
    @4
    cB
    cdig
    cfv
    co
    #
    cK
    cN
    wceq
    #
    c1
    cc0
    cif
    @3
    @6
    @10
    cB
    cmo
    @3
    @5
    @9
    cfl
    @3
    @9
    @5
    @3
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    @9
    @5
    wceq
    @0
    @1
    @16
    @2
    @0
    @14
    @15
    c2
    cB
    eluzelcn
    #
    @0
    cB
    cB
    eluz2nn
    #
    nnne0d
    #
    jca
    3ad2ant1
    @1
    @2
    @19
    @0
    @1
    @2
    wa
    #
    @18
    @17
    @1
    @18
    @2
    @17
    cK
    nn0z
    #
    cN
    nn0z
    #
    anim12i
    #
    ancomd
    3adant1
    cB
    cN
    cK
    expsub
    syl2anc
    eqcomd
    fveq2d
    oveq1d
    @3
    cB
    cn
    wcel
    #
    @1
    @4
    cc0
    cpnf
    cico
    co
    wcel
    #
    @12
    @7
    wceq
    @0
    @1
    @27
    @2
    @21
    3ad2ant1
    @0
    @1
    @2
    simp2
    @3
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    wa
    #
    @28
    @0
    @2
    @31
    @1
    @0
    @2
    wa
    #
    @29
    @30
    @0
    cB
    cr
    wcel
    #
    @2
    @29
    c2
    cB
    eluzelre
    #
    cB
    cN
    reexpcl
    sylan
    @32
    cB
    cN
    @0
    @33
    @2
    @34
    adantr
    @0
    @2
    simpr
    @0
    cc0
    cB
    cle
    wbr
    @2
    @0
    cB
    cB
    eluzge2nn0
    nn0ge0d
    adantr
    expge0d
    jca
    3adant2
    @4
    elrege0
    sylibr
    cB
    @4
    cK
    nn0digval
    syl3anc
    @3
    @13
    c1
    cc0
    @11
    @3
    @13
    wa
    #
    @11
    c1
    cB
    cmo
    co
    #
    c1
    @35
    @10
    c1
    cB
    cmo
    @35
    @10
    c1
    cfl
    cfv
    #
    c1
    @35
    @9
    c1
    cfl
    @35
    @9
    cB
    cc0
    cexp
    co
    #
    c1
    @35
    @8
    cc0
    cB
    cexp
    @35
    @8
    cc0
    wceq
    #
    cN
    cK
    wceq
    #
    @35
    cK
    cN
    @3
    @13
    simpr
    eqcomd
    @3
    @39
    @40
    wb
    @13
    @3
    cN
    cK
    @2
    @0
    cN
    cc
    wcel
    @1
    cN
    nn0cn
    3ad2ant3
    @1
    @0
    cK
    cc
    wcel
    @2
    cK
    nn0cn
    3ad2ant2
    subeq0ad
    adantr
    mpbird
    oveq2d
    @3
    @38
    c1
    wceq
    #
    @13
    @0
    @1
    @41
    @2
    @0
    cB
    @20
    exp0d
    3ad2ant1
    adantr
    eqtrd
    fveq2d
    @35
    c1
    cz
    wcel
    @37
    c1
    wceq
    @35
    1zzd
    c1
    flid
    syl
    eqtrd
    oveq1d
    @3
    @36
    c1
    wceq
    #
    @13
    @0
    @1
    @42
    @2
    @0
    @33
    c1
    cB
    clt
    wbr
    @42
    @34
    cB
    eluz2gt1
    cB
    1mod
    syl2anc
    3ad2ant1
    adantr
    eqtr2d
    @3
    @13
    wn
    #
    wa
    #
    @11
    cc0
    cN
    cK
    clt
    wbr
    #
    @44
    @11
    cc0
    wceq
    @45
    @44
    wa
    #
    @11
    cc0
    cB
    cmo
    co
    #
    cc0
    @46
    @10
    cc0
    cB
    cmo
    @46
    @9
    cc0
    c1
    cico
    co
    wcel
    #
    @10
    cc0
    wceq
    @46
    @0
    @8
    cz
    wcel
    #
    @8
    cc0
    clt
    wbr
    #
    @48
    @0
    @1
    @2
    @43
    @45
    simprl1
    @3
    @49
    @45
    @43
    @1
    @2
    @49
    @0
    @23
    cN
    cK
    @2
    @17
    @1
    @25
    adantl
    @1
    @18
    @2
    @24
    adantr
    zsubcld
    3adant1
    #
    ad2antrl
    @44
    @45
    @50
    @3
    @45
    @50
    wi
    @43
    @3
    @50
    @45
    @3
    cN
    cK
    @2
    @0
    cN
    cr
    wcel
    #
    @1
    cN
    nn0re
    #
    3ad2ant3
    @1
    @0
    cK
    cr
    wcel
    #
    @2
    cK
    nn0re
    #
    3ad2ant2
    sublt0d
    biimprd
    adantr
    impcom
    cB
    @8
    expnegico01
    syl3anc
    @9
    ico01fl0
    syl
    oveq1d
    @3
    @47
    cc0
    wceq
    #
    @45
    @43
    @0
    @1
    @56
    @2
    @0
    cB
    crp
    wcel
    #
    @56
    @0
    cB
    @21
    nnrpd
    #
    cB
    0mod
    syl
    3ad2ant1
    ad2antrl
    eqtrd
    @45
    wn
    #
    @44
    wa
    #
    @11
    @9
    cB
    cmo
    co
    #
    cc0
    @60
    @10
    @9
    cB
    cmo
    @60
    @9
    cz
    wcel
    #
    @10
    @9
    wceq
    @60
    cB
    cz
    wcel
    #
    @8
    cn0
    wcel
    #
    @62
    @3
    @63
    @59
    @43
    @0
    @1
    @63
    @2
    c2
    cB
    eluzelz
    3ad2ant1
    ad2antrl
    #
    @60
    cK
    cN
    cle
    wbr
    #
    @64
    @44
    @59
    @66
    @3
    @59
    @66
    wi
    #
    @43
    @1
    @2
    @67
    @0
    @23
    @59
    @66
    @23
    @54
    @52
    wa
    #
    @59
    @66
    wb
    @1
    @54
    @2
    @52
    @55
    @53
    anim12i
    #
    @68
    @66
    @59
    cK
    cN
    lenlt
    bicomd
    syl
    biimpd
    3adant1
    adantr
    impcom
    @60
    @23
    @66
    @64
    wb
    @3
    @23
    @59
    @43
    @0
    @1
    @2
    3simpc
    ad2antrl
    cK
    cN
    nn0sub
    syl
    mpbid
    cB
    @8
    zexpcl
    syl2anc
    @9
    flid
    syl
    oveq1d
    @60
    @61
    cc0
    wceq
    #
    @9
    cB
    cdiv
    co
    #
    cz
    wcel
    #
    @60
    @71
    cB
    @8
    c1
    cmin
    co
    #
    cexp
    co
    #
    cz
    @3
    @71
    @74
    wceq
    @59
    @43
    @3
    @74
    @71
    @3
    cB
    @8
    @0
    @1
    @14
    @2
    @20
    3ad2ant1
    @0
    @1
    @15
    @2
    @22
    3ad2ant1
    #
    @51
    expm1d
    eqcomd
    ad2antrl
    @60
    @63
    @73
    cn0
    wcel
    #
    @74
    cz
    wcel
    @65
    @60
    @8
    cn
    wcel
    #
    @76
    @60
    cK
    cN
    clt
    wbr
    #
    @77
    @44
    @59
    @78
    @3
    @43
    @59
    @78
    @43
    @59
    wa
    @13
    @45
    wo
    wn
    #
    @3
    @78
    @13
    @45
    pm4.56
    @3
    @78
    @79
    @3
    @68
    @78
    @79
    wb
    @1
    @2
    @68
    @0
    @69
    3adant1
    cK
    cN
    axlttri
    syl
    biimprd
    syl5bi
    expdimp
    impcom
    @60
    @18
    @17
    wa
    #
    @78
    @77
    wb
    @3
    @80
    @59
    @43
    @1
    @2
    @80
    @0
    @26
    3adant1
    ad2antrl
    cK
    cN
    znnsub
    syl
    mpbid
    @8
    nnm1nn0
    syl
    cB
    @73
    zexpcl
    syl2anc
    eqeltrd
    @3
    @70
    @72
    wb
    #
    @59
    @43
    @3
    @9
    cr
    wcel
    @57
    @81
    @3
    cB
    @8
    @0
    @1
    @33
    @2
    @34
    3ad2ant1
    @75
    @51
    reexpclzd
    @0
    @1
    @57
    @2
    @58
    3ad2ant1
    @9
    cB
    mod0
    syl2anc
    ad2antrl
    mpbird
    eqtrd
    pm2.61ian
    eqcomd
    ifeqda
    3eqtr4d
end
