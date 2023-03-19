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
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "w3a.mm"
include "simpll.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "elfzo0.mm"
include "lencl.mm"
include "cle.mm"
include "elfz2nn0.mm"
include "nn0addcl.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "com12.mm"
include "imp.mm"
include "cz.mm"
include "elnnz.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "posdif.mm"
include "syl2an.mm"
include "elnn0z.mm"
include "0red.mm"
include "zre.mm"
include "adantr.mm"
include "adantl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "nn0z.mm"
include "anim1i.mm"
include "sylibr.mm"
include "syld.mm"
include "expd.mm"
include "impancom.mm"
include "sylbi.mm"
include "sylbird.mm"
include "3ad2ant2.mm"
include "3adant3.mm"
include "ltaddsubd.mm"
include "exbiri.mm"
include "com23.mm"
include "3adant2.mm"
include "impcom.mm"
include "3jca.mm"
include "a1d.mm"
include "2a1i.mm"
include "eleq1.mm"
include "breq2.mm"
include "3anbi23d.mm"
include "imbi2d.mm"
include "3imtr4d.mm"
include "eqcoms.mm"
include "mpsyl.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "ccatval1.mm"
include "syl.mm"
include "swrdccatin12lem2c.mm"
include "simprl.mm"
include "swrdfv.mm"
include "syl2anc.mm"
include "eleq1i.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "eluzfz2.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "sylbir.mm"
include "ad3antrrr.mm"
include "simprr.mm"
include "syl31anc.mm"
include "3eqtr4d.mm"

theorem swrdccatin12lem3
  let cA: class A
  let cB: class B
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( ( A e. Word V /\ B e. Word V ) /\ ( M e. ( 0 ... L ) /\ N e. ( L ... ( L + ( # ` B ) ) ) ) ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ K e. ( 0 ..^ ( L - M ) ) ) -> ( ( ( A ++ B ) substr <. M , N >. ) ` K ) = ( ( A substr <. M , L >. ) ` K ) ) )

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
    #
    wcel
    #
    cN
    cL
    cL
    cB
    chash
    cfv
    caddc
    co
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
    cfv
    #
    wceq
    @8
    @12
    wa
    #
    cK
    cM
    caddc
    co
    #
    @13
    cfv
    #
    @17
    cA
    cfv
    #
    @14
    @15
    @16
    @1
    @2
    @17
    cc0
    cA
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    w3a
    #
    @18
    @19
    wceq
    @16
    @3
    @21
    @22
    @3
    @7
    @12
    simpll
    @16
    @17
    cn0
    wcel
    #
    @20
    cn
    wcel
    #
    @17
    @20
    clt
    wbr
    #
    w3a
    #
    @21
    @12
    @8
    @26
    @11
    @8
    @26
    wi
    #
    @9
    @11
    cK
    cn0
    wcel
    #
    @10
    cn
    wcel
    #
    cK
    @10
    clt
    wbr
    #
    w3a
    #
    @27
    cK
    @10
    elfzo0
    @8
    @31
    @26
    @3
    @7
    @31
    @26
    wi
    #
    @1
    @7
    @32
    wi
    #
    @2
    cL
    @20
    wceq
    @1
    @20
    cn0
    wcel
    #
    @33
    swrdccatin12.l
    cV
    cA
    lencl
    #
    @34
    @33
    wi
    @20
    cL
    @20
    cL
    wceq
    #
    cL
    cn0
    wcel
    #
    @7
    @31
    @23
    cL
    cn
    wcel
    #
    @17
    cL
    clt
    wbr
    #
    w3a
    #
    wi
    #
    wi
    #
    @34
    @33
    @42
    @36
    @37
    @5
    @6
    @41
    @5
    cM
    cn0
    wcel
    #
    @37
    cM
    cL
    cle
    wbr
    #
    w3a
    #
    @6
    @41
    wi
    cM
    cL
    elfz2nn0
    @45
    @41
    @6
    @45
    @31
    @40
    @45
    @31
    wa
    @23
    @38
    @39
    @45
    @31
    @23
    @43
    @37
    @31
    @23
    wi
    @44
    @31
    @43
    @23
    @28
    @29
    @43
    @23
    wi
    @30
    @28
    @43
    @23
    cK
    cM
    nn0addcl
    ex
    3ad2ant1
    com12
    3ad2ant1
    imp
    @45
    @31
    @38
    @43
    @37
    @31
    @38
    wi
    @44
    @31
    @43
    @37
    wa
    #
    @38
    @29
    @28
    @46
    @38
    wi
    #
    @30
    @29
    @10
    cz
    wcel
    #
    cc0
    @10
    clt
    wbr
    #
    wa
    @47
    @10
    elnnz
    @49
    @47
    @48
    @46
    @49
    @38
    @46
    @49
    cM
    cL
    clt
    wbr
    #
    @38
    @43
    cM
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    @50
    @49
    wb
    @37
    cM
    nn0re
    #
    cL
    nn0re
    #
    cM
    cL
    posdif
    syl2an
    @43
    @37
    @50
    @38
    wi
    #
    @43
    cM
    cz
    wcel
    #
    cc0
    cM
    cle
    wbr
    #
    wa
    @37
    @55
    wi
    cM
    elnn0z
    @56
    @37
    @57
    @55
    @56
    @37
    wa
    #
    @57
    @50
    @38
    @58
    @57
    @50
    wa
    #
    cc0
    cL
    clt
    wbr
    #
    @38
    @58
    cc0
    cr
    wcel
    @51
    @52
    @59
    @60
    wi
    @58
    0red
    @56
    @51
    @37
    cM
    zre
    adantr
    @37
    @52
    @56
    @54
    adantl
    cc0
    cM
    cL
    lelttr
    syl3anc
    @37
    @60
    @38
    wi
    @56
    @37
    @60
    @38
    @37
    @60
    wa
    cL
    cz
    wcel
    #
    @60
    wa
    @38
    @37
    @61
    @60
    cL
    nn0z
    anim1i
    cL
    elnnz
    sylibr
    ex
    adantl
    syld
    expd
    impancom
    sylbi
    imp
    sylbird
    com12
    adantl
    sylbi
    3ad2ant2
    com12
    3adant3
    imp
    @31
    @45
    @39
    @28
    @30
    @45
    @39
    wi
    #
    @29
    @28
    @30
    @62
    @28
    @45
    @30
    @39
    @28
    @45
    @39
    @30
    @28
    @45
    wa
    cK
    cM
    cL
    @28
    cK
    cr
    wcel
    @45
    cK
    nn0re
    adantr
    @45
    @51
    @28
    @43
    @37
    @51
    @44
    @53
    3ad2ant1
    adantl
    @45
    @52
    @28
    @37
    @43
    @52
    @44
    @54
    3ad2ant2
    adantl
    ltaddsubd
    exbiri
    com23
    imp
    3adant2
    impcom
    3jca
    ex
    a1d
    sylbi
    imp
    2a1i
    @20
    cL
    cn0
    eleq1
    @36
    @32
    @41
    @7
    @36
    @26
    @40
    @31
    @36
    @24
    @38
    @25
    @39
    @23
    @20
    cL
    cn
    eleq1
    @20
    cL
    @17
    clt
    breq2
    3anbi23d
    imbi2d
    imbi2d
    3imtr4d
    eqcoms
    mpsyl
    adantr
    imp
    com12
    sylbi
    adantl
    impcom
    @17
    @20
    elfzo0
    sylibr
    @1
    @2
    @21
    df-3an
    sylanbrc
    cV
    cA
    cB
    @17
    ccatval1
    syl
    @16
    @13
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
    @13
    chash
    cfv
    cfz
    co
    wcel
    w3a
    #
    @9
    @14
    @18
    wceq
    @8
    @63
    @12
    cA
    cB
    cL
    cM
    cN
    cV
    swrdccatin12.l
    swrdccatin12lem2c
    adantr
    @8
    @9
    @11
    simprl
    cV
    @13
    cM
    cN
    cK
    swrdfv
    syl2anc
    @16
    @1
    @5
    cL
    cc0
    @20
    cfz
    co
    #
    wcel
    #
    @11
    @15
    @19
    wceq
    @8
    @1
    @12
    @1
    @2
    @7
    simpll
    adantr
    @8
    @5
    @12
    @3
    @5
    @6
    simprl
    adantr
    @1
    @65
    @2
    @7
    @12
    @1
    @34
    @65
    @35
    @34
    @37
    @65
    cL
    @20
    cn0
    swrdccatin12.l
    eleq1i
    @37
    cL
    @4
    @64
    @37
    cL
    cc0
    cuz
    cfv
    wcel
    cL
    @4
    wcel
    cL
    elnn0uz
    cc0
    cL
    eluzfz2
    sylbi
    @20
    cL
    cc0
    cfz
    cL
    @20
    swrdccatin12.l
    eqcomi
    oveq2i
    syl6eleqr
    sylbir
    syl
    ad3antrrr
    @8
    @9
    @11
    simprr
    cV
    cA
    cM
    cL
    cK
    swrdfv
    syl31anc
    3eqtr4d
    ex
end
