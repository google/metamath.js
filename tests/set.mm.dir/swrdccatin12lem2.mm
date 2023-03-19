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
include "adantl.mm"
include "syl5com.mm"
include "impcom.mm"
include "fveq2d.mm"
include "swrdccatin12lem2a.mm"
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
include "elfz2.mm"
include "zsubcl.mm"
include "cr.mm"
include "zre.mm"
include "subge0.mm"
include "syl2anr.mm"
include "biimprd.mm"
include "elnn0z.mm"
include "expcom.mm"
include "com12.mm"
include "3adant2.mm"
include "0elfz.mm"
include "lencl.mm"
include "elfzel2.mm"
include "expcomd.mm"
include "3ad2ant3.mm"
include "nn0re.mm"
include "3jca.mm"
include "lesubadd2.mm"
include "com13.mm"
include "3imtr4g.mm"
include "com23.mm"
include "swrdccatin12lem2b.mm"
include "syl31anc.mm"
include "3eqtr4d.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "eluzfz2.mm"
include "syl5eqel.mm"
include "swrdlen.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem swrdccatin12lem2
  let cA: class A
  let cB: class B
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( ( A e. Word V /\ B e. Word V ) /\ ( M e. ( 0 ... L ) /\ N e. ( L ... ( L + ( # ` B ) ) ) ) ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ -. K e. ( 0 ..^ ( L - M ) ) ) -> ( ( ( A ++ B ) substr <. M , N >. ) ` K ) = ( ( B substr <. 0 , ( N - L ) >. ) ` ( K - ( # ` ( A substr <. M , L >. ) ) ) ) ) )

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
    cc0
    cN
    cL
    cmin
    co
    #
    cop
    csubstr
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
    swrdccatin12.l
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
    @8
    @34
    @33
    wi
    #
    @3
    @4
    @35
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
    @35
    cM
    cL
    elfz2nn0
    @36
    @37
    @35
    @38
    @36
    @37
    wa
    #
    @34
    @33
    cL
    @28
    wceq
    #
    @39
    @34
    wa
    #
    @33
    wi
    swrdccatin12.l
    @41
    @33
    @40
    @23
    cL
    cmin
    co
    #
    @31
    wceq
    #
    @39
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
    @43
    @34
    @36
    @44
    @37
    @45
    cM
    nn0cn
    cL
    nn0cn
    anim12i
    cK
    zcn
    @46
    @47
    wa
    #
    @31
    @25
    @42
    @48
    @25
    @48
    @47
    @12
    cc
    wcel
    #
    wa
    #
    @25
    cc
    wcel
    @47
    @46
    @50
    @46
    @49
    @47
    @45
    @44
    @49
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
    @48
    cK
    cL
    cM
    @46
    @47
    simpr
    @44
    @45
    @47
    simplr
    @44
    @45
    @47
    simpll
    subsub3d
    eqtr2d
    syl2an
    @40
    @29
    @42
    @31
    @29
    @42
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
    adantr
    adantl
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
    @53
    @54
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
    @53
    @9
    @14
    @56
    @8
    @14
    @56
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
    @40
    @53
    @56
    wb
    #
    swrdccatin12.l
    @57
    @28
    cL
    @28
    cL
    wceq
    #
    @52
    @55
    @23
    @58
    @28
    cL
    @51
    @6
    cfzo
    @58
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
    @53
    df-3an
    sylanbrc
    cV
    cA
    cB
    @23
    ccatval2
    syl
    @22
    @2
    cc0
    cc0
    @19
    cfz
    co
    wcel
    #
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
    cc0
    cmin
    co
    cfzo
    co
    wcel
    #
    @26
    @32
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
    @59
    @14
    @8
    @59
    @3
    @8
    @19
    cn0
    wcel
    #
    @59
    @7
    @62
    @4
    @7
    cL
    cz
    wcel
    #
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
    @62
    cN
    cL
    @6
    elfz2
    #
    @66
    @69
    @62
    @63
    @65
    @69
    @62
    wi
    @64
    @69
    @63
    @65
    wa
    #
    @62
    @67
    @72
    @62
    wi
    @68
    @72
    @67
    @62
    @72
    @67
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
    @62
    @72
    @73
    @67
    @65
    @63
    @73
    cN
    cL
    zsubcl
    ancoms
    adantr
    @72
    @67
    @74
    @72
    @74
    @67
    @65
    cN
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    @74
    @67
    wb
    @63
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
    #
    com12
    3adant2
    imp
    sylbi
    adantl
    @19
    0elfz
    syl
    adantl
    adantr
    @9
    @60
    @14
    @3
    @8
    @60
    @2
    @8
    @60
    wi
    @1
    @2
    @5
    cn0
    wcel
    #
    @8
    @60
    cV
    cB
    lencl
    @4
    @7
    @80
    @60
    wi
    #
    @4
    @63
    @7
    @81
    wi
    cM
    cc0
    cL
    elfzel2
    @63
    @80
    @7
    @60
    @63
    @80
    @7
    @60
    wi
    @63
    @80
    wa
    #
    @70
    @62
    @80
    @19
    @5
    cle
    wbr
    #
    w3a
    #
    @7
    @60
    @82
    @70
    @84
    @82
    @70
    wa
    @62
    @80
    @83
    @82
    @70
    @62
    @63
    @70
    @62
    wi
    @80
    @70
    @63
    @62
    @66
    @69
    @63
    @62
    wi
    #
    @65
    @63
    @69
    @85
    wi
    @64
    @69
    @65
    @85
    @69
    @63
    @65
    @62
    @79
    expcomd
    com12
    3ad2ant3
    imp
    com12
    adantr
    imp
    @63
    @80
    @70
    simplr
    @70
    @82
    @83
    @69
    @66
    @82
    @83
    wi
    #
    @68
    @66
    @86
    wi
    @67
    @82
    @66
    @68
    @83
    @82
    @66
    @68
    @83
    wi
    #
    @82
    @66
    wa
    #
    @75
    @76
    @5
    cr
    wcel
    #
    w3a
    #
    @87
    @88
    @75
    @76
    @89
    @66
    @75
    @82
    @65
    @63
    @75
    @64
    @77
    3ad2ant3
    adantl
    @82
    @76
    @66
    @63
    @76
    @80
    @78
    adantr
    adantr
    @82
    @89
    @66
    @80
    @89
    @63
    @5
    nn0re
    adantl
    adantr
    3jca
    @90
    @83
    @68
    cN
    cL
    @5
    lesubadd2
    biimprd
    syl
    ex
    com13
    adantl
    impcom
    impcom
    3jca
    ex
    @71
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
    @61
    @8
    @14
    @61
    wi
    @3
    cK
    cL
    cM
    cN
    @6
    swrdccatin12lem2b
    adantl
    imp
    cV
    cB
    cc0
    @19
    @25
    swrdfv
    syl31anc
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
    @93
    @14
    @9
    @1
    @4
    @92
    @1
    @2
    @8
    simpll
    @3
    @4
    @7
    simprl
    @3
    @92
    @8
    @1
    @92
    @2
    @1
    @28
    cn0
    wcel
    #
    @92
    cV
    cA
    lencl
    @94
    cL
    @28
    @91
    swrdccatin12.l
    @94
    @28
    cc0
    cuz
    cfv
    wcel
    @28
    @91
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
