include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "cc0.mm"
include "cmin.mm"
include "wral.mm"
include "clsw.mm"
include "ccsh.mm"
include "wb.mm"
include "cz.mm"
include "wceq.mm"
include "elfzoelz.mm"
include "cshwlen.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "adantr.mm"
include "cmo.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "cuz.mm"
include "wss.mm"
include "cn0.mm"
include "lencl.mm"
include "cle.mm"
include "wbr.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "nn0re.mm"
include "lem1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "sselda.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "cn.mm"
include "clt.mm"
include "elfzo1.mm"
include "simp2bi.mm"
include "adantl.mm"
include "elfzom1p1elfzo.mm"
include "sylan.mm"
include "preq12d.mm"
include "adantlr.mm"
include "c2.mm"
include "w3a.mm"
include "2z.mm"
include "a1i.mm"
include "nnz.mm"
include "3ad2ant2.mm"
include "wne.mm"
include "nnnn0.mm"
include "nnne0.mm"
include "1red.mm"
include "cr.mm"
include "nnre.mm"
include "3ad2ant1.mm"
include "nnge1.mm"
include "simp3.mm"
include "lelttrd.mm"
include "gtned.mm"
include "nn0n0n1ge2.mm"
include "sylbi.mm"
include "ad3antlr.mm"
include "simplrl.mm"
include "wi.mm"
include "lsw.mm"
include "preq1d.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "clwwisshclwwslemlem.mm"
include "syl311anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"

theorem clwwisshclwwslem
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cN: class N
  let cV: class V
  let cW: class W

  disjoint E i
  disjoint E j
  disjoint i j
  disjoint N i
  disjoint N j
  disjoint V i
  disjoint V j
  disjoint W i
  disjoint W j
  assert |- ( ( W e. Word V /\ N e. ( 1 ..^ ( # ` W ) ) ) -> ( ( A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) -> A. j e. ( 0 ..^ ( ( # ` ( W cyclShift N ) ) - 1 ) ) { ( ( W cyclShift N ) ` j ) , ( ( W cyclShift N ) ` ( j + 1 ) ) } e. E ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cN
    c1
    cW
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    wa
    #
    vi
    cv
    #
    cW
    cfv
    @5
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @2
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cW
    clsw
    cfv
    #
    cc0
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vj
    cv
    #
    cW
    cN
    ccsh
    co
    #
    cfv
    #
    @14
    c1
    caddc
    co
    #
    @15
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vj
    cc0
    @15
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    @4
    @13
    wa
    #
    @20
    vj
    @23
    @24
    @14
    @23
    wcel
    #
    @14
    @7
    wcel
    #
    @20
    @4
    @25
    @26
    wb
    @13
    @4
    @23
    @7
    @14
    @4
    @22
    @6
    cc0
    cfzo
    @4
    @21
    @2
    c1
    cmin
    @3
    @1
    cN
    cz
    wcel
    #
    @21
    @2
    wceq
    cN
    c1
    @2
    elfzoelz
    #
    cN
    cV
    cW
    cshwlen
    sylan2
    oveq1d
    oveq2d
    eleq2d
    adantr
    @24
    @26
    @20
    @24
    @26
    wa
    #
    @19
    @14
    cN
    caddc
    co
    @2
    cmo
    co
    cW
    cfv
    #
    @17
    cN
    caddc
    co
    @2
    cmo
    co
    cW
    cfv
    #
    cpr
    #
    cE
    @4
    @26
    @19
    @32
    wceq
    @13
    @4
    @26
    wa
    #
    @16
    @30
    @18
    @31
    @33
    @1
    @27
    @14
    cc0
    @2
    cfzo
    co
    #
    wcel
    @16
    @30
    wceq
    @1
    @3
    @26
    simpll
    #
    @3
    @27
    @1
    @26
    @28
    ad2antlr
    #
    @4
    @7
    @34
    @14
    @4
    @2
    @6
    cuz
    cfv
    wcel
    #
    @7
    @34
    wss
    @1
    @37
    @3
    @1
    @2
    cn0
    wcel
    #
    @37
    cV
    cW
    lencl
    @38
    @6
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @6
    @2
    cle
    wbr
    @37
    @38
    @40
    @39
    @2
    nn0z
    #
    @2
    peano2zm
    syl
    @41
    @38
    @2
    @2
    nn0re
    lem1d
    @6
    @2
    eluz2
    syl3anbrc
    syl
    adantr
    @6
    cc0
    @2
    fzoss2
    syl
    sselda
    @14
    cN
    cV
    cW
    cshwidxmod
    syl3anc
    @33
    @1
    @27
    @17
    @34
    wcel
    #
    @18
    @31
    wceq
    @35
    @36
    @4
    @2
    cn
    wcel
    #
    @26
    @42
    @3
    @43
    @1
    @3
    cN
    cn
    wcel
    #
    @43
    cN
    @2
    clt
    wbr
    #
    @2
    cN
    elfzo1
    #
    simp2bi
    adantl
    @2
    @14
    elfzom1p1elfzo
    sylan
    @17
    cN
    cV
    cW
    cshwidxmod
    syl3anc
    preq12d
    adantlr
    @29
    @2
    c2
    cuz
    cfv
    wcel
    #
    @14
    cz
    wcel
    #
    @27
    @8
    @6
    cW
    cfv
    #
    @10
    cpr
    #
    cE
    wcel
    #
    @32
    cE
    wcel
    @3
    @47
    @1
    @13
    @26
    @3
    @44
    @43
    @45
    w3a
    #
    @47
    @46
    @52
    c2
    cz
    wcel
    #
    @40
    c2
    @2
    cle
    wbr
    #
    @47
    @53
    @52
    2z
    a1i
    @43
    @44
    @40
    @45
    @2
    nnz
    3ad2ant2
    @52
    @38
    @2
    cc0
    wne
    #
    @2
    c1
    wne
    @54
    @43
    @44
    @38
    @45
    @2
    nnnn0
    3ad2ant2
    @43
    @44
    @55
    @45
    @2
    nnne0
    3ad2ant2
    @52
    c1
    @2
    @52
    1red
    #
    @52
    c1
    cN
    @2
    @56
    @44
    @43
    cN
    cr
    wcel
    @45
    cN
    nnre
    3ad2ant1
    @43
    @44
    @2
    cr
    wcel
    @45
    @2
    nnre
    3ad2ant2
    @44
    @43
    c1
    cN
    cle
    wbr
    @45
    cN
    nnge1
    3ad2ant1
    @44
    @43
    @45
    simp3
    lelttrd
    gtned
    @2
    nn0n0n1ge2
    syl3anc
    c2
    @2
    eluz2
    syl3anbrc
    sylbi
    ad3antlr
    @26
    @48
    @24
    @14
    cc0
    @6
    elfzoelz
    adantl
    @3
    @27
    @1
    @13
    @26
    @28
    ad3antlr
    @4
    @8
    @12
    @26
    simplrl
    @24
    @51
    @26
    @13
    @4
    @51
    @12
    @4
    @51
    wi
    @8
    @4
    @12
    @51
    @4
    @11
    @50
    cE
    @4
    @9
    @49
    @10
    @1
    @9
    @49
    wceq
    @3
    cW
    @0
    lsw
    adantr
    preq1d
    eleq1d
    biimpcd
    adantl
    impcom
    adantr
    @14
    cN
    cE
    vi
    @2
    cW
    clwwisshclwwslemlem
    syl311anc
    eqeltrd
    ex
    sylbid
    ralrimiv
    ex
end
