include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "c1.mm"
include "2nn.mm"
include "simpl.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "simpr.mm"
include "congrep.mm"
include "syl2anc.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "ad2antrl.mm"
include "nnre.mm"
include "ad2antrr.mm"
include "cle.mm"
include "elfzle1.mm"
include "anim1i.mm"
include "wb.mm"
include "0zd.mm"
include "nnz.mm"
include "elfz.mm"
include "syl3anc.mm"
include "adantr.mm"
include "mpbird.mm"
include "simplrr.mm"
include "orcd.mm"
include "weq.mm"
include "id.mm"
include "eqidd.mm"
include "acongeq12d.mm"
include "rspcev.mm"
include "simplll.mm"
include "simplrl.mm"
include "w3a.mm"
include "3ad2ant2.mm"
include "2re.mm"
include "remulcl.mm"
include "3ad2ant1.mm"
include "clt.mm"
include "2z.mm"
include "zmulcl.mm"
include "simp2.mm"
include "elfzm11.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "simp3d.mm"
include "ltled.mm"
include "subge0d.mm"
include "wceq.mm"
include "cc.mm"
include "nncn.mm"
include "caddc.mm"
include "2times.mm"
include "oveq1d.mm"
include "pncan2.mm"
include "anidms.mm"
include "eqtrd.mm"
include "syl.mm"
include "simp3.mm"
include "eqbrtrd.mm"
include "subled.mm"
include "jca.mm"
include "zsubcld.mm"
include "simplr.mm"
include "simprr.mm"
include "congsym.mm"
include "syl22anc.mm"
include "dvdsadd.mm"
include "mpbid.mm"
include "zcnd.mm"
include "zcn.mm"
include "ad2antlr.mm"
include "subnegd.mm"
include "recnd.mm"
include "subadd23d.mm"
include "breqtrrd.mm"
include "olcd.mm"
include "lecasei.mm"
include "rexlimddv.mm"

theorem acongrep
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b

  disjoint A a
  disjoint N a
  disjoint A b
  disjoint a b
  disjoint N b
  assert |- ( ( A e. NN /\ N e. ZZ ) -> E. a e. ( 0 ... A ) ( ( 2 x. A ) || ( a - N ) \/ ( 2 x. A ) || ( a - -u N ) ) )

  proof
    cA
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    c2
    cA
    cmul
    co
    #
    vb
    cv
    #
    cN
    cmin
    co
    cdvds
    wbr
    #
    @3
    va
    cv
    #
    cN
    cmin
    co
    cdvds
    wbr
    @3
    @6
    cN
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    va
    cc0
    cA
    cfz
    co
    #
    wrex
    #
    vb
    cc0
    @3
    c1
    cmin
    co
    #
    cfz
    co
    #
    @2
    @3
    cn
    wcel
    #
    @1
    @5
    vb
    @12
    wrex
    @2
    c2
    cn
    wcel
    @0
    @13
    2nn
    @0
    @1
    simpl
    c2
    cA
    nnmulcl
    sylancr
    @0
    @1
    simpr
    @3
    cN
    vb
    congrep
    syl2anc
    @2
    @4
    @12
    wcel
    #
    @5
    wa
    #
    wa
    #
    @10
    @4
    cA
    @14
    @4
    cr
    wcel
    #
    @2
    @5
    @14
    @4
    @4
    cc0
    @11
    elfzelz
    #
    zred
    #
    ad2antrl
    #
    @0
    cA
    cr
    wcel
    #
    @1
    @15
    cA
    nnre
    #
    ad2antrr
    @16
    @4
    cA
    cle
    wbr
    #
    wa
    #
    @4
    @9
    wcel
    #
    @5
    @3
    @4
    @7
    cmin
    co
    cdvds
    wbr
    #
    wo
    #
    @10
    @24
    @25
    cc0
    @4
    cle
    wbr
    #
    @23
    wa
    #
    @16
    @28
    @23
    @14
    @28
    @2
    @5
    @4
    cc0
    @11
    elfzle1
    ad2antrl
    anim1i
    @16
    @25
    @29
    wb
    #
    @23
    @16
    @4
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @30
    @14
    @31
    @2
    @5
    @18
    ad2antrl
    #
    @16
    0zd
    #
    @0
    @33
    @1
    @15
    cA
    nnz
    #
    ad2antrr
    #
    @4
    cc0
    cA
    elfz
    syl3anc
    adantr
    mpbird
    @24
    @5
    @26
    @2
    @14
    @5
    @23
    simplrr
    orcd
    @8
    @27
    va
    @4
    @9
    va
    vb
    weq
    #
    @3
    @6
    @4
    cN
    cN
    @38
    id
    @38
    cN
    eqidd
    acongeq12d
    rspcev
    syl2anc
    @16
    cA
    @4
    cle
    wbr
    #
    wa
    #
    @3
    @4
    cmin
    co
    #
    @9
    wcel
    #
    @3
    @41
    cN
    cmin
    co
    cdvds
    wbr
    #
    @3
    @41
    @7
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    #
    @10
    @40
    @42
    cc0
    @41
    cle
    wbr
    #
    @41
    cA
    cle
    wbr
    #
    wa
    #
    @40
    @0
    @14
    @39
    @49
    @0
    @1
    @15
    @39
    simplll
    @2
    @14
    @5
    @39
    simplrl
    @16
    @39
    simpr
    @0
    @14
    @39
    w3a
    #
    @47
    @48
    @50
    @47
    @4
    @3
    cle
    wbr
    @50
    @4
    @3
    @14
    @0
    @17
    @39
    @19
    3ad2ant2
    #
    @0
    @14
    @3
    cr
    wcel
    #
    @39
    @0
    c2
    cr
    wcel
    @21
    @52
    2re
    @22
    c2
    cA
    remulcl
    sylancr
    3ad2ant1
    #
    @50
    @31
    @28
    @4
    @3
    clt
    wbr
    #
    @50
    @32
    @3
    cz
    wcel
    #
    @14
    @31
    @28
    @54
    w3a
    #
    @50
    0zd
    @0
    @14
    @55
    @39
    @0
    c2
    cz
    wcel
    #
    @33
    @55
    2z
    @36
    c2
    cA
    zmulcl
    #
    sylancr
    3ad2ant1
    @0
    @14
    @39
    simp2
    @32
    @55
    wa
    @14
    @56
    @4
    cc0
    @3
    elfzm11
    biimpa
    syl21anc
    simp3d
    ltled
    @50
    @3
    @4
    @53
    @51
    subge0d
    mpbird
    @50
    @3
    cA
    @4
    @53
    @0
    @14
    @21
    @39
    @22
    3ad2ant1
    @51
    @50
    @3
    cA
    cmin
    co
    #
    cA
    @4
    cle
    @0
    @14
    @59
    cA
    wceq
    #
    @39
    @0
    cA
    cc
    wcel
    #
    @60
    cA
    nncn
    @61
    @59
    cA
    cA
    caddc
    co
    #
    cA
    cmin
    co
    #
    cA
    @61
    @3
    @62
    cA
    cmin
    cA
    2times
    oveq1d
    @61
    @63
    cA
    wceq
    cA
    cA
    pncan2
    anidms
    eqtrd
    syl
    3ad2ant1
    @0
    @14
    @39
    simp3
    eqbrtrd
    subled
    jca
    syl3anc
    @16
    @42
    @49
    wb
    #
    @39
    @16
    @41
    cz
    wcel
    @32
    @33
    @64
    @16
    @3
    @4
    @16
    @57
    @33
    @55
    2z
    @37
    @58
    sylancr
    #
    @34
    zsubcld
    #
    @35
    @37
    @41
    cc0
    cA
    elfz
    syl3anc
    adantr
    mpbird
    @40
    @45
    @43
    @16
    @45
    @39
    @16
    @3
    @3
    cN
    @4
    cmin
    co
    #
    caddc
    co
    #
    @44
    cdvds
    @16
    @3
    @67
    cdvds
    wbr
    #
    @3
    @68
    cdvds
    wbr
    #
    @16
    @55
    @31
    @1
    @5
    @69
    @65
    @34
    @0
    @1
    @15
    simplr
    #
    @2
    @14
    @5
    simprr
    @3
    @4
    cN
    congsym
    syl22anc
    @16
    @55
    @67
    cz
    wcel
    @69
    @70
    wb
    @65
    @16
    cN
    @4
    @71
    @34
    zsubcld
    @3
    @67
    dvdsadd
    syl2anc
    mpbid
    @16
    @44
    @41
    cN
    caddc
    co
    @68
    @16
    @41
    cN
    @16
    @41
    @66
    zcnd
    @1
    cN
    cc
    wcel
    @0
    @15
    cN
    zcn
    ad2antlr
    #
    subnegd
    @16
    @3
    @4
    cN
    @16
    @3
    @65
    zcnd
    @16
    @4
    @20
    recnd
    @72
    subadd23d
    eqtrd
    breqtrrd
    adantr
    olcd
    @8
    @46
    va
    @41
    @9
    @6
    @41
    wceq
    #
    @3
    @6
    @41
    cN
    cN
    @73
    id
    @73
    cN
    eqidd
    acongeq12d
    rspcev
    syl2anc
    lecasei
    rexlimddv
end
