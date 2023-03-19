include "cmin.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "cc0.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "breq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "cuz.mm"
include "wss.mm"
include "cfzo.mm"
include "cz.mm"
include "0zd.mm"
include "elfzoel2.mm"
include "elfzoelz.mm"
include "zsubcld.mm"
include "peano2zd.mm"
include "cn.mm"
include "clt.mm"
include "w3a.mm"
include "elfzo1.mm"
include "cr.mm"
include "wi.mm"
include "nnre.mm"
include "posdif.mm"
include "0red.mm"
include "resubcl.mm"
include "ancoms.mm"
include "ltle.mm"
include "syl2anc.mm"
include "lep1d.mm"
include "1red.mm"
include "readdcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syld.mm"
include "sylbid.mm"
include "syl2an.mm"
include "3impia.mm"
include "sylbi.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "syl.mm"
include "fzss1.mm"
include "sselda.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmptd.mm"
include "wn.mm"
include "elfz2.mm"
include "zre.mm"
include "anim12i.mm"
include "simprr.mm"
include "simpl.mm"
include "resubcld.mm"
include "ltp1d.mm"
include "ltletr.mm"
include "mpand.mm"
include "ltnled.mm"
include "sylibd.mm"
include "expcom.mm"
include "3adant1.mm"
include "com12.mm"
include "com13.mm"
include "adantr.mm"
include "impcom.mm"
include "syl5bi.mm"
include "imp.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem crctcshwlkn0lem3
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cJ: class J
  let cN: class N
  assume crctcshwlkn0lem.s: |- ( ph -> S e. ( 1 ..^ N ) )
  assume crctcshwlkn0lem.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint J x
  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  assert |- ( ( ph /\ J e. ( ( ( N - S ) + 1 ) ... N ) ) -> ( Q ` J ) = ( P ` ( ( J + S ) - N ) ) )

  proof
    wph
    cJ
    cN
    cS
    cmin
    co
    #
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cJ
    cQ
    cfv
    cJ
    @0
    cle
    wbr
    #
    cJ
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @6
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    @9
    @4
    vx
    cJ
    vx
    cv
    #
    @0
    cle
    wbr
    #
    @11
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @13
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    @10
    cc0
    cN
    cfz
    co
    #
    cQ
    cvv
    cQ
    vx
    @18
    @17
    cmpt
    wceq
    @4
    crctcshwlkn0lem.q
    a1i
    @11
    cJ
    wceq
    #
    @17
    @10
    wceq
    @4
    @19
    @12
    @5
    @14
    @16
    @7
    @9
    @11
    cJ
    @0
    cle
    breq1
    @19
    @13
    @6
    cP
    @11
    cJ
    cS
    caddc
    oveq1
    #
    fveq2d
    @19
    @15
    @8
    cP
    @19
    @13
    @6
    cN
    cmin
    @20
    oveq1d
    fveq2d
    ifbieq12d
    adantl
    wph
    @2
    @18
    cJ
    wph
    @1
    cc0
    cuz
    cfv
    wcel
    #
    @2
    @18
    wss
    wph
    cS
    c1
    cN
    cfzo
    co
    wcel
    #
    @21
    crctcshwlkn0lem.s
    @22
    cc0
    cz
    wcel
    @1
    cz
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @21
    @22
    0zd
    @22
    @0
    @22
    cN
    cS
    cS
    c1
    cN
    elfzoel2
    cS
    c1
    cN
    elfzoelz
    #
    zsubcld
    peano2zd
    @22
    cS
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cS
    cN
    clt
    wbr
    #
    w3a
    @24
    cN
    cS
    elfzo1
    @26
    @27
    @28
    @24
    @26
    cS
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @28
    @24
    wi
    @27
    cS
    nnre
    cN
    nnre
    @29
    @30
    wa
    #
    @28
    cc0
    @0
    clt
    wbr
    #
    @24
    cS
    cN
    posdif
    @31
    @32
    cc0
    @0
    cle
    wbr
    #
    @24
    @31
    cc0
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @32
    @33
    wi
    @31
    0red
    #
    @30
    @29
    @35
    cN
    cS
    resubcl
    ancoms
    #
    cc0
    @0
    ltle
    syl2anc
    @31
    @33
    @0
    @1
    cle
    wbr
    #
    @24
    @31
    @0
    @37
    lep1d
    @31
    @34
    @35
    @1
    cr
    wcel
    #
    @33
    @38
    wa
    @24
    wi
    @36
    @37
    @31
    @0
    c1
    @37
    @31
    1red
    readdcld
    cc0
    @0
    @1
    letr
    syl3anc
    mpan2d
    syld
    sylbid
    syl2an
    3impia
    sylbi
    cc0
    @1
    eluz2
    syl3anbrc
    syl
    @1
    cc0
    cN
    fzss1
    syl
    sselda
    @10
    cvv
    wcel
    @4
    @5
    @7
    @9
    @6
    cP
    fvex
    @8
    cP
    fvex
    ifex
    a1i
    fvmptd
    @4
    @5
    @7
    @9
    wph
    @3
    @5
    wn
    #
    wph
    @22
    @3
    @40
    wi
    crctcshwlkn0lem.s
    @3
    @23
    cN
    cz
    wcel
    #
    cJ
    cz
    wcel
    #
    w3a
    #
    @1
    cJ
    cle
    wbr
    #
    cJ
    cN
    cle
    wbr
    #
    wa
    #
    wa
    #
    @22
    @40
    cJ
    @1
    cN
    elfz2
    @47
    @22
    @40
    @46
    @43
    @22
    @40
    wi
    #
    @44
    @43
    @48
    wi
    @45
    @22
    @43
    @44
    @40
    @22
    cS
    cz
    wcel
    #
    @43
    @44
    @40
    wi
    #
    wi
    @25
    @43
    @49
    @50
    @41
    @42
    @49
    @50
    wi
    #
    @23
    @42
    @41
    @51
    @49
    @42
    @41
    wa
    #
    @50
    @49
    @29
    cJ
    cr
    wcel
    #
    @30
    wa
    #
    @50
    @52
    cS
    zre
    @42
    @53
    @41
    @30
    cJ
    zre
    cN
    zre
    anim12i
    @29
    @54
    wa
    #
    @44
    @0
    cJ
    clt
    wbr
    #
    @40
    @55
    @0
    @1
    clt
    wbr
    #
    @44
    @56
    @55
    @0
    @55
    cN
    cS
    @29
    @53
    @30
    simprr
    @29
    @54
    simpl
    resubcld
    #
    ltp1d
    @55
    @35
    @39
    @53
    @57
    @44
    wa
    @56
    wi
    @58
    @55
    @0
    c1
    @58
    @55
    1red
    readdcld
    @54
    @53
    @29
    @53
    @30
    simpl
    adantl
    #
    @0
    @1
    cJ
    ltletr
    syl3anc
    mpand
    @55
    @0
    cJ
    @58
    @59
    ltnled
    sylibd
    syl2an
    expcom
    ancoms
    3adant1
    com12
    syl
    com13
    adantr
    impcom
    com12
    syl5bi
    syl
    imp
    iffalsed
    eqtrd
end
