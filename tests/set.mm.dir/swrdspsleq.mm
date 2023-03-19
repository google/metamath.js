include "cle.mm"
include "wbr.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "wb.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpl.mm"
include "swrdsb0eq.mm"
include "syl3anc.mm"
include "wi.mm"
include "c0.mm"
include "ral0.mm"
include "cz.mm"
include "nn0z.mm"
include "fzon.mm"
include "syl2an.mm"
include "biimpa.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "impcom.mm"
include "2thd.mm"
include "wn.mm"
include "cc0.mm"
include "swrdcl.mm"
include "eqwrd.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "swrdsbslen.mm"
include "biantrurd.mm"
include "cr.mm"
include "nn0re.mm"
include "clt.mm"
include "ltnle.mm"
include "ltle.mm"
include "sylbird.mm"
include "cmin.mm"
include "cuz.mm"
include "simpl1l.mm"
include "adantr.mm"
include "anim12i.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eluz2.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "3jca.mm"
include "swrdlen2.mm"
include "syl.mm"
include "oveq2d.mm"
include "wsbc.mm"
include "caddc.mm"
include "0zd.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "fzoshftral.mm"
include "cc.mm"
include "nn0cn.mm"
include "addid2.mm"
include "npcan.mm"
include "oveq12d.mm"
include "cvv.mm"
include "ovex.mm"
include "csb.mm"
include "sbceqg.mm"
include "csbfv2g.mm"
include "csbvarg.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "bitrd.mm"
include "mp1i.mm"
include "swrdfv2.mm"
include "sylan.mm"
include "simpl1r.mm"
include "simpl3r.mm"
include "ralbidva.mm"
include "syld.mm"
include "3bitr2d.mm"
include "pm2.61ian.mm"

theorem swrdspsleq
  let cU: class U
  let vi: setvar i
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vj: setvar j

  disjoint M i
  disjoint N i
  disjoint U i
  disjoint V i
  disjoint W i
  disjoint M j
  disjoint i j
  disjoint N j
  disjoint U j
  disjoint W j
  assert |- ( ( ( W e. Word V /\ U e. Word V ) /\ ( M e. NN0 /\ N e. NN0 ) /\ ( N <_ ( # ` W ) /\ N <_ ( # ` U ) ) ) -> ( ( W substr <. M , N >. ) = ( U substr <. M , N >. ) <-> A. i e. ( M ..^ N ) ( W ` i ) = ( U ` i ) ) )

  proof
    cN
    cM
    cle
    wbr
    #
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @1
    wcel
    #
    wa
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cW
    chash
    cfv
    cle
    wbr
    #
    cN
    cU
    chash
    cfv
    cle
    wbr
    #
    wa
    #
    w3a
    #
    cW
    cM
    cN
    cop
    #
    csubstr
    co
    #
    cU
    @12
    csubstr
    co
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    #
    @16
    cU
    cfv
    #
    wceq
    #
    vi
    cM
    cN
    cfzo
    co
    #
    wral
    #
    wb
    @0
    @11
    wa
    #
    @15
    @21
    @22
    @4
    @7
    @0
    @15
    @0
    @4
    @7
    @10
    simpr1
    @0
    @4
    @7
    @10
    simpr2
    @0
    @11
    simpl
    cU
    cM
    cN
    cV
    cW
    swrdsb0eq
    syl3anc
    @11
    @0
    @21
    @7
    @4
    @0
    @21
    wi
    @10
    @7
    @0
    @21
    @7
    @0
    wa
    #
    @21
    @19
    vi
    c0
    wral
    @19
    vi
    ral0
    @23
    @19
    vi
    @20
    c0
    @7
    @0
    @20
    c0
    wceq
    #
    @5
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @0
    @24
    wb
    @6
    cM
    nn0z
    #
    cN
    nn0z
    #
    cM
    cN
    fzon
    syl2an
    biimpa
    raleqdv
    mpbiri
    ex
    3ad2ant2
    impcom
    2thd
    @0
    wn
    #
    @11
    wa
    #
    @15
    @13
    chash
    cfv
    #
    @14
    chash
    cfv
    wceq
    #
    vj
    cv
    #
    @13
    cfv
    #
    @33
    @14
    cfv
    #
    wceq
    #
    vj
    cc0
    @31
    cfzo
    co
    #
    wral
    #
    wa
    #
    @38
    @21
    @11
    @15
    @39
    wb
    #
    @29
    @4
    @7
    @40
    @10
    @2
    @13
    @1
    wcel
    @14
    @1
    wcel
    @40
    @3
    cV
    cW
    cM
    cN
    swrdcl
    cV
    cU
    cM
    cN
    swrdcl
    @13
    vj
    cV
    @14
    eqwrd
    syl2an
    3ad2ant1
    adantl
    @30
    @32
    @38
    @11
    @32
    @29
    cU
    cM
    cN
    cV
    cW
    swrdsbslen
    adantl
    biantrurd
    @11
    @29
    @38
    @21
    wb
    #
    @11
    @29
    cM
    cN
    cle
    wbr
    #
    @41
    @7
    @4
    @29
    @42
    wi
    #
    @10
    @5
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @43
    @6
    cM
    nn0re
    cN
    nn0re
    @44
    @45
    wa
    @29
    cM
    cN
    clt
    wbr
    @42
    cM
    cN
    ltnle
    cM
    cN
    ltle
    sylbird
    syl2an
    3ad2ant2
    @11
    @42
    @41
    @11
    @42
    wa
    #
    @38
    @36
    vj
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @21
    @46
    @36
    vj
    @37
    @48
    @46
    @31
    @47
    cc0
    cfzo
    @46
    @2
    @5
    cN
    cM
    cuz
    cfv
    wcel
    #
    wa
    #
    @8
    w3a
    #
    @31
    @47
    wceq
    @46
    @2
    @51
    @8
    @2
    @3
    @7
    @10
    @42
    simpl1l
    @46
    @5
    @50
    @11
    @5
    @42
    @7
    @4
    @5
    @10
    @5
    @6
    simpl
    3ad2ant2
    adantr
    @46
    @25
    @26
    @42
    w3a
    #
    @50
    @46
    @25
    @26
    wa
    #
    @42
    wa
    @53
    @11
    @54
    @42
    @7
    @4
    @54
    @10
    @5
    @25
    @6
    @26
    @27
    @28
    anim12i
    3ad2ant2
    anim1i
    @25
    @26
    @42
    df-3an
    sylibr
    cM
    cN
    eluz2
    sylibr
    jca
    #
    @11
    @8
    @42
    @10
    @4
    @8
    @7
    @8
    @9
    simpl
    3ad2ant3
    adantr
    3jca
    #
    cW
    cM
    cN
    cV
    swrdlen2
    syl
    oveq2d
    raleqdv
    @46
    @49
    @36
    vj
    @16
    cM
    cmin
    co
    #
    wsbc
    #
    vi
    cc0
    cM
    caddc
    co
    #
    @47
    cM
    caddc
    co
    #
    cfzo
    co
    #
    wral
    #
    @21
    @11
    @49
    @62
    wb
    #
    @42
    @11
    cc0
    cz
    wcel
    @47
    cz
    wcel
    #
    @25
    @63
    @11
    0zd
    @7
    @4
    @64
    @10
    @6
    @26
    @25
    @64
    @5
    @28
    @27
    cN
    cM
    zsubcl
    syl2anr
    3ad2ant2
    @7
    @4
    @25
    @10
    @5
    @25
    @6
    @27
    adantr
    3ad2ant2
    @36
    vj
    vi
    cM
    cc0
    @47
    fzoshftral
    syl3anc
    adantr
    @46
    @62
    @58
    vi
    @20
    wral
    @21
    @46
    @58
    vi
    @61
    @20
    @11
    @61
    @20
    wceq
    #
    @42
    @7
    @4
    @65
    @10
    @6
    cN
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    @65
    @5
    cN
    nn0cn
    cM
    nn0cn
    @66
    @67
    wa
    @59
    cM
    @60
    cN
    cfzo
    @67
    @59
    cM
    wceq
    @66
    cM
    addid2
    adantl
    cN
    cM
    npcan
    oveq12d
    syl2anr
    3ad2ant2
    adantr
    raleqdv
    @46
    @58
    @19
    vi
    @20
    @46
    @16
    @20
    wcel
    #
    wa
    #
    @58
    @57
    @13
    cfv
    #
    @57
    @14
    cfv
    #
    wceq
    #
    @19
    @57
    cvv
    wcel
    #
    @58
    @72
    wb
    @69
    @16
    cM
    cmin
    ovex
    @73
    @58
    vj
    @57
    @34
    csb
    #
    vj
    @57
    @35
    csb
    #
    wceq
    @72
    vj
    @57
    @34
    @35
    cvv
    sbceqg
    @73
    @74
    @70
    @75
    @71
    @73
    @74
    vj
    @57
    @33
    csb
    #
    @13
    cfv
    @70
    vj
    @57
    @33
    cvv
    @13
    csbfv2g
    @73
    @76
    @57
    @13
    vj
    @57
    cvv
    csbvarg
    #
    fveq2d
    eqtrd
    @73
    @75
    @76
    @14
    cfv
    @71
    vj
    @57
    @33
    cvv
    @14
    csbfv2g
    @73
    @76
    @57
    @14
    @77
    fveq2d
    eqtrd
    eqeq12d
    bitrd
    mp1i
    @69
    @70
    @17
    @71
    @18
    @46
    @52
    @68
    @70
    @17
    wceq
    @56
    cW
    cM
    cN
    cV
    @16
    swrdfv2
    sylan
    @46
    @3
    @51
    @9
    w3a
    @68
    @71
    @18
    wceq
    @46
    @3
    @51
    @9
    @2
    @3
    @7
    @10
    @42
    simpl1r
    @55
    @8
    @9
    @4
    @7
    @42
    simpl3r
    3jca
    cU
    cM
    cN
    cV
    @16
    swrdfv2
    sylan
    eqeq12d
    bitrd
    ralbidva
    bitrd
    bitrd
    bitrd
    ex
    syld
    impcom
    3bitr2d
    pm2.61ian
end
