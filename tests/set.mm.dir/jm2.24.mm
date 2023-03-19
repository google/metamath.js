include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crmy.mm"
include "caddc.mm"
include "crmx.mm"
include "clt.mm"
include "simpll.mm"
include "peano2zm.mm"
include "ad2antlr.mm"
include "frmy.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "zred.mm"
include "cr.mm"
include "adantr.mm"
include "readdcld.mm"
include "0red.mm"
include "cn0.mm"
include "frmx.mm"
include "nn0red.mm"
include "cneg.mm"
include "znegcl.mm"
include "peano2zd.mm"
include "wceq.mm"
include "rmy0.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "zre.mm"
include "le0neg1d.mm"
include "mpbid.mm"
include "wb.mm"
include "0zd.mm"
include "zleltp1.mm"
include "ltrmy.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"
include "lermy.mm"
include "addgtge0.mm"
include "syl22anc.mm"
include "recnd.mm"
include "negdid.mm"
include "rmyneg.mm"
include "oveq12d.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "negsubdi.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "breqtrrd.mm"
include "lt0neg1d.mm"
include "mpbird.mm"
include "nn0ge0d.mm"
include "ltletrd.mm"
include "cn.mm"
include "elnnz.mm"
include "biimpri.mm"
include "adantll.mm"
include "jm2.24nn.mm"
include "wo.mm"
include "adantl.mm"
include "0re.mm"
include "lelttric.mm"
include "mpjaodan.mm"

theorem jm2.24
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmY ( N - 1 ) ) + ( A rmY N ) ) < ( A rmX N ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cc0
    cle
    wbr
    #
    cA
    cN
    c1
    cmin
    co
    #
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    caddc
    co
    #
    cA
    cN
    crmx
    co
    #
    clt
    wbr
    #
    cc0
    cN
    clt
    wbr
    #
    @3
    @4
    wa
    #
    @8
    cc0
    @9
    @12
    @6
    @7
    @12
    @6
    @12
    @1
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    @1
    @2
    @4
    simpll
    #
    @2
    @13
    @1
    @4
    cN
    peano2zm
    ad2antlr
    #
    cA
    @5
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zred
    #
    @3
    @7
    cr
    wcel
    @4
    @3
    @7
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    adantr
    #
    readdcld
    #
    @12
    0red
    @12
    @9
    @3
    @9
    cn0
    wcel
    @4
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    adantr
    #
    nn0red
    @12
    @8
    cc0
    clt
    wbr
    cc0
    @8
    cneg
    #
    clt
    wbr
    @12
    cc0
    cA
    cN
    cneg
    #
    c1
    caddc
    co
    #
    crmy
    co
    #
    cA
    @21
    crmy
    co
    #
    caddc
    co
    #
    @20
    clt
    @12
    @23
    cr
    wcel
    @24
    cr
    wcel
    cc0
    @23
    clt
    wbr
    cc0
    @24
    cle
    wbr
    cc0
    @25
    clt
    wbr
    @12
    @23
    @12
    @1
    @22
    cz
    wcel
    #
    @23
    cz
    wcel
    @14
    @12
    @21
    @2
    @21
    cz
    wcel
    #
    @1
    @4
    cN
    znegcl
    ad2antlr
    #
    peano2zd
    #
    cA
    @22
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zred
    @12
    @24
    @12
    @1
    @27
    @24
    cz
    wcel
    @14
    @28
    cA
    @21
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zred
    @12
    cA
    cc0
    crmy
    co
    #
    cc0
    @23
    clt
    @1
    @30
    cc0
    wceq
    @2
    @4
    cA
    rmy0
    ad2antrr
    #
    @12
    cc0
    @22
    clt
    wbr
    #
    @30
    @23
    clt
    wbr
    #
    @12
    cc0
    @21
    cle
    wbr
    #
    @32
    @12
    @4
    @34
    @3
    @4
    simpr
    @12
    cN
    @2
    cN
    cr
    wcel
    #
    @1
    @4
    cN
    zre
    #
    ad2antlr
    le0neg1d
    mpbid
    #
    @12
    cc0
    cz
    wcel
    #
    @27
    @34
    @32
    wb
    @12
    0zd
    #
    @28
    cc0
    @21
    zleltp1
    syl2anc
    mpbid
    @12
    @1
    @38
    @26
    @32
    @33
    wb
    @14
    @39
    @29
    cA
    cc0
    @22
    ltrmy
    syl3anc
    mpbid
    eqbrtrrd
    @12
    @30
    cc0
    @24
    cle
    @31
    @12
    @34
    @30
    @24
    cle
    wbr
    #
    @37
    @12
    @1
    @38
    @27
    @34
    @40
    wb
    @14
    @39
    @28
    cA
    cc0
    @21
    lermy
    syl3anc
    mpbid
    eqbrtrrd
    @23
    @24
    addgtge0
    syl22anc
    @12
    @20
    @6
    cneg
    #
    @7
    cneg
    #
    caddc
    co
    cA
    @5
    cneg
    #
    crmy
    co
    #
    @24
    caddc
    co
    @25
    @12
    @6
    @7
    @12
    @6
    @16
    recnd
    @12
    @7
    @17
    recnd
    negdid
    @12
    @44
    @41
    @24
    @42
    caddc
    @12
    @1
    @13
    @44
    @41
    wceq
    @14
    @15
    cA
    @5
    rmyneg
    syl2anc
    @3
    @24
    @42
    wceq
    @4
    cA
    cN
    rmyneg
    adantr
    oveq12d
    @12
    @44
    @23
    @24
    caddc
    @12
    @43
    @22
    cA
    crmy
    @12
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    @43
    @22
    wceq
    @2
    @45
    @1
    @4
    cN
    zcn
    ad2antlr
    ax-1cn
    cN
    c1
    negsubdi
    sylancl
    oveq2d
    oveq1d
    3eqtr2d
    breqtrrd
    @12
    @8
    @18
    lt0neg1d
    mpbird
    @12
    @9
    @19
    nn0ge0d
    ltletrd
    @3
    @11
    wa
    @1
    cN
    cn
    wcel
    #
    @10
    @1
    @2
    @11
    simpll
    @2
    @11
    @46
    @1
    @46
    @2
    @11
    wa
    cN
    elnnz
    biimpri
    adantll
    cA
    cN
    jm2.24nn
    syl2anc
    @3
    @35
    cc0
    cr
    wcel
    @4
    @11
    wo
    @2
    @35
    @1
    @36
    adantl
    0re
    cN
    cc0
    lelttric
    sylancl
    mpjaodan
end
