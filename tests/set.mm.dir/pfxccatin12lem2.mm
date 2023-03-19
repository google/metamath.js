include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cmin.mm"
include "cfzo.mm"
include "wn.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "cpfx.mm"
include "wceq.mm"
include "w3a.mm"
include "swrdccatin12lem2c.mm"
include "adantr.mm"
include "simprl.mm"
include "swrdfv.mm"
include "syl2anc.mm"
include "wi.mm"
include "cz.mm"
include "elfzoelz.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "elfz2nn0.mm"
include "cc.mm"
include "nn0cn.mm"
include "anim12i.mm"
include "zcn.mm"
include "subcl.mm"
include "ancoms.mm"
include "anim2i.mm"
include "syl.mm"
include "addid1d.mm"
include "simpr.mm"
include "simplr.mm"
include "simpll.mm"
include "subsub3d.mm"
include "eqtr2d.mm"
include "syl2an.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "ax-mp.mm"
include "ex.mm"
include "3adant3.mm"
include "sylbi.mm"
include "ad2antrl.mm"
include "syl5com.mm"
include "impcom.mm"
include "fveq2d.mm"
include "swrdccatin12lem2a.mm"
include "adantl.mm"
include "imp.mm"
include "wb.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "sylibr.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "ccatval2.mm"
include "lencl.mm"
include "elfzel2.mm"
include "zsubcl.mm"
include "cr.mm"
include "zre.mm"
include "subge0.mm"
include "syl2anr.mm"
include "biimprd.mm"
include "elnn0z.mm"
include "expcom.mm"
include "expcomd.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "nn0re.mm"
include "lesubadd2.mm"
include "syl3anc.mm"
include "com13.mm"
include "3jca.mm"
include "elfz2.mm"
include "3imtr4g.mm"
include "com23.mm"
include "pfxccatin12lem1.mm"
include "pfxfv.mm"
include "zcnd.mm"
include "elfzelz.mm"
include "subcld.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "eluzfz2.mm"
include "syl5eqel.mm"
include "swrdlen.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem pfxccatin12lem2
  let cA: class A
  let cB: class B
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume pfxccatin12.l: |- L = ( # ` A )


  assert |- ( ( ( A e. Word V /\ B e. Word V ) /\ ( M e. ( 0 ... L ) /\ N e. ( L ... ( L + ( # ` B ) ) ) ) ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ -. K e. ( 0 ..^ ( L - M ) ) ) -> ( ( ( A ++ B ) substr <. M , N >. ) ` K ) = ( ( B prefix ( N - L ) ) ` ( K - ( # ` ( A substr <. M , L >. ) ) ) ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cM
    cc0
    cL
    cfz
    co
    wcel
    #
    cN
    cL
    cL
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    wa
    #
    cK
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    cK
    cc0
    cL
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    wn
    #
    wa
    #
    cK
    cA
    cB
    cconcat
    co
    #
    cM
    cN
    cop
    csubstr
    co
    cfv
    #
    cK
    cA
    cM
    cL
    cop
    csubstr
    co
    chash
    cfv
    #
    cmin
    co
    #
    cB
    cN
    cL
    cmin
    co
    #
    cpfx
    co
    #
    cfv
    #
    wceq
    @9
    @14
    wa
    #
    @16
    cK
    cM
    caddc
    co
    #
    @15
    cfv
    #
    cK
    @12
    cmin
    co
    #
    @20
    cfv
    #
    @21
    @22
    @15
    @0
    wcel
    cM
    cc0
    cN
    cfz
    co
    wcel
    cN
    cc0
    @15
    chash
    cfv
    cfz
    co
    wcel
    w3a
    #
    @11
    @16
    @24
    wceq
    @9
    @27
    @14
    cA
    cB
    cL
    cM
    cN
    cV
    pfxccatin12.l
    swrdccatin12lem2c
    adantr
    @9
    @11
    @13
    simprl
    cV
    @15
    cM
    cN
    cK
    swrdfv
    syl2anc
    @22
    @23
    cA
    chash
    cfv
    #
    cmin
    co
    #
    cB
    cfv
    #
    @25
    cc0
    caddc
    co
    #
    cB
    cfv
    #
    @24
    @26
    @22
    @29
    @31
    cB
    @14
    @9
    @29
    @31
    wceq
    #
    @11
    @9
    @33
    wi
    @13
    @11
    cK
    cz
    wcel
    #
    @9
    @33
    cK
    cc0
    @10
    elfzoelz
    #
    @4
    @34
    @33
    wi
    #
    @3
    @7
    @4
    cM
    cn0
    wcel
    #
    cL
    cn0
    wcel
    #
    cM
    cL
    cle
    wbr
    #
    w3a
    @36
    cM
    cL
    elfz2nn0
    @37
    @38
    @36
    @39
    @37
    @38
    wa
    #
    @34
    @33
    cL
    @28
    wceq
    #
    @40
    @34
    wa
    #
    @33
    wi
    pfxccatin12.l
    @42
    @33
    @41
    @23
    cL
    cmin
    co
    #
    @31
    wceq
    #
    @40
    cM
    cc
    wcel
    #
    cL
    cc
    wcel
    #
    wa
    #
    cK
    cc
    wcel
    #
    @44
    @34
    @37
    @45
    @38
    @46
    cM
    nn0cn
    cL
    nn0cn
    anim12i
    cK
    zcn
    @47
    @48
    wa
    #
    @31
    @25
    @43
    @49
    @25
    @49
    @48
    @12
    cc
    wcel
    #
    wa
    #
    @25
    cc
    wcel
    @48
    @47
    @51
    @47
    @50
    @48
    @46
    @45
    @50
    cL
    cM
    subcl
    ancoms
    anim2i
    ancoms
    cK
    @12
    subcl
    syl
    addid1d
    @49
    cK
    cL
    cM
    @47
    @48
    simpr
    @45
    @46
    @48
    simplr
    @45
    @46
    @48
    simpll
    subsub3d
    eqtr2d
    syl2an
    @41
    @29
    @43
    @31
    @29
    @43
    wceq
    @28
    cL
    @28
    cL
    @23
    cmin
    oveq2
    eqcoms
    eqeq1d
    syl5ibr
    ax-mp
    ex
    3adant3
    sylbi
    ad2antrl
    syl5com
    adantr
    impcom
    fveq2d
    @22
    @1
    @2
    @23
    @28
    @28
    @5
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    @24
    @30
    wceq
    @22
    @3
    @54
    @55
    @3
    @8
    @14
    simpll
    @22
    @23
    cL
    @6
    cfzo
    co
    #
    wcel
    #
    @54
    @9
    @14
    @57
    @8
    @14
    @57
    wi
    @3
    cK
    cL
    cM
    cN
    @6
    swrdccatin12lem2a
    adantl
    imp
    @41
    @54
    @57
    wb
    #
    pfxccatin12.l
    @58
    @28
    cL
    @28
    cL
    wceq
    #
    @53
    @56
    @23
    @59
    @28
    cL
    @52
    @6
    cfzo
    @59
    id
    @28
    cL
    @5
    caddc
    oveq1
    oveq12d
    eleq2d
    eqcoms
    ax-mp
    sylibr
    @1
    @2
    @54
    df-3an
    sylanbrc
    cV
    cA
    cB
    @23
    ccatval2
    syl
    @22
    @26
    @25
    cB
    cfv
    #
    @32
    @22
    @2
    @19
    cc0
    @5
    cfz
    co
    wcel
    #
    @25
    cc0
    @19
    cfzo
    co
    wcel
    #
    @26
    @60
    wceq
    @9
    @2
    @14
    @1
    @2
    @8
    simplr
    adantr
    @9
    @61
    @14
    @3
    @8
    @61
    @2
    @8
    @61
    wi
    @1
    @2
    @5
    cn0
    wcel
    #
    @8
    @61
    cV
    cB
    lencl
    @4
    @7
    @63
    @61
    wi
    #
    @4
    cL
    cz
    wcel
    #
    @7
    @64
    wi
    cM
    cc0
    cL
    elfzel2
    #
    @65
    @63
    @7
    @61
    @65
    @63
    @7
    @61
    wi
    @65
    @63
    wa
    #
    @65
    @6
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cL
    cN
    cle
    wbr
    #
    cN
    @6
    cle
    wbr
    #
    wa
    #
    wa
    #
    @19
    cn0
    wcel
    #
    @63
    @19
    @5
    cle
    wbr
    #
    w3a
    #
    @7
    @61
    @67
    @74
    @77
    @67
    @74
    wa
    @75
    @63
    @76
    @67
    @74
    @75
    @65
    @74
    @75
    wi
    @63
    @74
    @65
    @75
    @70
    @73
    @65
    @75
    wi
    #
    @69
    @65
    @73
    @78
    wi
    @68
    @73
    @69
    @78
    @73
    @65
    @69
    @75
    @71
    @65
    @69
    wa
    #
    @75
    wi
    @72
    @79
    @71
    @75
    @79
    @71
    wa
    @19
    cz
    wcel
    #
    cc0
    @19
    cle
    wbr
    #
    @75
    @79
    @80
    @71
    @69
    @65
    @80
    cN
    cL
    zsubcl
    ancoms
    adantr
    @79
    @71
    @81
    @79
    @81
    @71
    @69
    cN
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    @81
    @71
    wb
    @65
    cN
    zre
    #
    cL
    zre
    #
    cN
    cL
    subge0
    syl2anr
    biimprd
    imp
    @19
    elnn0z
    sylanbrc
    expcom
    adantr
    expcomd
    com12
    3ad2ant3
    imp
    com12
    adantr
    imp
    @65
    @63
    @74
    simplr
    @74
    @67
    @76
    @73
    @70
    @67
    @76
    wi
    #
    @72
    @70
    @86
    wi
    @71
    @67
    @70
    @72
    @76
    @67
    @70
    @72
    @76
    wi
    #
    @67
    @70
    wa
    @82
    @83
    @5
    cr
    wcel
    #
    @87
    @70
    @82
    @67
    @69
    @65
    @82
    @68
    @84
    3ad2ant3
    adantl
    @67
    @83
    @70
    @65
    @83
    @63
    @85
    adantr
    adantr
    @67
    @88
    @70
    @63
    @88
    @65
    @5
    nn0re
    adantl
    adantr
    @82
    @83
    @88
    w3a
    @76
    @72
    cN
    cL
    @5
    lesubadd2
    biimprd
    syl3anc
    ex
    com13
    adantl
    impcom
    impcom
    3jca
    ex
    cN
    cL
    @6
    elfz2
    @19
    @5
    elfz2nn0
    3imtr4g
    ex
    com23
    syl
    imp
    syl5com
    adantl
    imp
    adantr
    @9
    @14
    @62
    @8
    @14
    @62
    wi
    @3
    cK
    cL
    cM
    cN
    @6
    pfxccatin12lem1
    adantl
    imp
    @25
    @19
    cV
    cB
    pfxfv
    syl3anc
    @22
    @25
    @31
    cB
    @22
    @31
    @25
    @22
    @25
    @22
    cK
    @12
    @11
    @48
    @9
    @13
    @11
    cK
    @35
    zcnd
    ad2antrl
    @22
    cL
    cM
    @9
    @46
    @14
    @4
    @46
    @3
    @7
    @4
    cL
    @66
    zcnd
    ad2antrl
    adantr
    @9
    @45
    @14
    @4
    @45
    @3
    @7
    @4
    cM
    cM
    cc0
    cL
    elfzelz
    zcnd
    ad2antrl
    adantr
    subcld
    subcld
    addid1d
    eqcomd
    fveq2d
    eqtrd
    3eqtr4d
    @22
    @25
    @18
    @20
    @22
    @12
    @17
    cK
    cmin
    @22
    @17
    @12
    @22
    @1
    @4
    cL
    cc0
    @28
    cfz
    co
    #
    wcel
    #
    w3a
    #
    @17
    @12
    wceq
    @9
    @91
    @14
    @9
    @1
    @4
    @90
    @1
    @2
    @8
    simpll
    @3
    @4
    @7
    simprl
    @3
    @90
    @8
    @1
    @90
    @2
    @1
    @28
    cn0
    wcel
    #
    @90
    cV
    cA
    lencl
    @92
    cL
    @28
    @89
    pfxccatin12.l
    @92
    @28
    cc0
    cuz
    cfv
    wcel
    @28
    @89
    wcel
    @28
    elnn0uz
    cc0
    @28
    eluzfz2
    sylbi
    syl5eqel
    syl
    adantr
    adantr
    3jca
    adantr
    cV
    cA
    cM
    cL
    swrdlen
    syl
    eqcomd
    oveq2d
    fveq2d
    3eqtrd
    ex
end
