include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cdiv.mm"
include "cexp.mm"
include "c4.mm"
include "cc.mm"
include "wceq.mm"
include "2cn.mm"
include "simpll.mm"
include "simprl.mm"
include "remulcl.mm"
include "syl2anc.mm"
include "mulge0.mm"
include "resqrtcl.mm"
include "recnd.mm"
include "sqmul.mm"
include "sylancr.mm"
include "sq2.mm"
include "oveq1i.mm"
include "sqrtth.mm"
include "syl.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "cmin.mm"
include "resubcld.mm"
include "sqge0d.mm"
include "binom2.mm"
include "binom2sub.mm"
include "oveq12d.mm"
include "resqcld.mm"
include "2re.mm"
include "readdcld.mm"
include "pnpcan2d.mm"
include "2timesd.mm"
include "2t2e4.mm"
include "2cnd.mm"
include "mulassd.mm"
include "syl5eqr.mm"
include "pnncand.mm"
include "3eqtr4rd.mm"
include "3eqtrd.mm"
include "wb.mm"
include "4re.mm"
include "subsub23.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "subge0d.mm"
include "eqbrtrd.mm"
include "sqrtge0.mm"
include "0le2.mm"
include "mpanl12.mm"
include "addge0.mm"
include "an4s.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "clt.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "lemuldiv2.mm"

theorem amgm2
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( sqrt ` ( A x. B ) ) <_ ( ( A + B ) / 2 ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    c2
    cA
    cB
    cmul
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cA
    cB
    caddc
    co
    #
    cle
    wbr
    #
    @8
    @10
    c2
    cdiv
    co
    cle
    wbr
    #
    @6
    @11
    @9
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    cle
    wbr
    @6
    @13
    c4
    @7
    cmul
    co
    #
    @14
    cle
    @6
    @13
    c2
    c2
    cexp
    co
    #
    @8
    c2
    cexp
    co
    #
    cmul
    co
    #
    @15
    @6
    c2
    cc
    wcel
    @8
    cc
    wcel
    @13
    @18
    wceq
    2cn
    @6
    @8
    @6
    @7
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @8
    cr
    wcel
    #
    @6
    @0
    @3
    @19
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    cA
    cB
    remulcl
    syl2anc
    #
    cA
    cB
    mulge0
    #
    @7
    resqrtcl
    syl2anc
    #
    recnd
    c2
    @8
    sqmul
    sylancr
    @6
    @18
    c4
    @17
    cmul
    co
    @15
    @16
    c4
    @17
    cmul
    sq2
    oveq1i
    @6
    @17
    @7
    c4
    cmul
    @6
    @7
    cc
    wcel
    @17
    @7
    wceq
    @6
    @7
    @24
    recnd
    #
    @7
    sqrtth
    syl
    oveq2d
    syl5eq
    eqtrd
    @6
    cc0
    @14
    @15
    cmin
    co
    #
    cle
    wbr
    @15
    @14
    cle
    wbr
    @6
    cc0
    cA
    cB
    cmin
    co
    #
    c2
    cexp
    co
    #
    @28
    cle
    @6
    @29
    @6
    cA
    cB
    @22
    @23
    resubcld
    #
    sqge0d
    @6
    @14
    @30
    cmin
    co
    #
    @15
    wceq
    #
    @28
    @30
    wceq
    #
    @6
    @32
    cA
    c2
    cexp
    co
    #
    c2
    @7
    cmul
    co
    #
    caddc
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    @35
    @36
    cmin
    co
    #
    @38
    caddc
    co
    #
    cmin
    co
    @37
    @40
    cmin
    co
    #
    @15
    @6
    @14
    @39
    @30
    @41
    cmin
    @6
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @14
    @39
    wceq
    @6
    cA
    @22
    recnd
    #
    @6
    cB
    @23
    recnd
    #
    cA
    cB
    binom2
    syl2anc
    @6
    @43
    @44
    @30
    @41
    wceq
    @45
    @46
    cA
    cB
    binom2sub
    syl2anc
    oveq12d
    @6
    @37
    @40
    @38
    @6
    @37
    @6
    @35
    @36
    @6
    cA
    @22
    resqcld
    #
    @6
    c2
    cr
    wcel
    #
    @19
    @36
    cr
    wcel
    2re
    @24
    c2
    @7
    remulcl
    sylancr
    #
    readdcld
    recnd
    @6
    @40
    @6
    @35
    @36
    @47
    @49
    resubcld
    recnd
    @6
    @38
    @6
    cB
    @23
    resqcld
    recnd
    pnpcan2d
    @6
    c2
    @36
    cmul
    co
    #
    @36
    @36
    caddc
    co
    @15
    @42
    @6
    @36
    @6
    @36
    @49
    recnd
    #
    2timesd
    @6
    @15
    c2
    c2
    cmul
    co
    #
    @7
    cmul
    co
    @50
    @52
    c4
    @7
    cmul
    2t2e4
    oveq1i
    @6
    c2
    c2
    @7
    @6
    2cnd
    #
    @53
    @27
    mulassd
    syl5eqr
    @6
    @35
    @36
    @36
    @6
    @35
    @47
    recnd
    @51
    @51
    pnncand
    3eqtr4rd
    3eqtrd
    @6
    @14
    cc
    wcel
    @30
    cc
    wcel
    @15
    cc
    wcel
    @33
    @34
    wb
    @6
    @14
    @6
    @10
    @6
    cA
    cB
    @22
    @23
    readdcld
    #
    resqcld
    #
    recnd
    @6
    @30
    @6
    @29
    @31
    resqcld
    recnd
    @6
    @15
    @6
    c4
    cr
    wcel
    @19
    @15
    cr
    wcel
    4re
    @24
    c4
    @7
    remulcl
    sylancr
    #
    recnd
    @14
    @30
    @15
    subsub23
    syl3anc
    mpbid
    breqtrrd
    @6
    @14
    @15
    @55
    @56
    subge0d
    mpbid
    eqbrtrd
    @6
    @9
    @10
    @6
    @48
    @21
    @9
    cr
    wcel
    2re
    @26
    c2
    @8
    remulcl
    sylancr
    @54
    @6
    @21
    cc0
    @8
    cle
    wbr
    #
    cc0
    @9
    cle
    wbr
    #
    @26
    @6
    @19
    @20
    @57
    @24
    @25
    @7
    sqrtge0
    syl2anc
    @48
    cc0
    c2
    cle
    wbr
    @21
    @57
    wa
    @58
    2re
    0le2
    c2
    @8
    mulge0
    mpanl12
    syl2anc
    @0
    @3
    @1
    @4
    cc0
    @10
    cle
    wbr
    cA
    cB
    addge0
    an4s
    le2sqd
    mpbird
    @6
    @21
    @10
    cr
    wcel
    @48
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @11
    @12
    wb
    @26
    @54
    @60
    @6
    @48
    @59
    2re
    2pos
    pm3.2i
    a1i
    @8
    @10
    c2
    lemuldiv2
    syl3anc
    mpbid
end
