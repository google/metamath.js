include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cre.mm"
include "cfv.mm"
include "ccj.mm"
include "c2.mm"
include "cdiv.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "syl2an.mm"
include "reval.mm"
include "syl.mm"
include "cjcl.mm"
include "addcld.mm"
include "halfcld.mm"
include "adantr.mm"
include "cmin.mm"
include "cc0.mm"
include "recl.mm"
include "eqeltrrd.mm"
include "simpl.mm"
include "resubcld.mm"
include "a1i.mm"
include "adantl.mm"
include "subcld.mm"
include "subdid.mm"
include "pnpcand.mm"
include "pnpcan2d.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "addsubd.mm"
include "subsubd.mm"
include "3eqtr4d.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "2cn.mm"
include "wne.mm"
include "2ne0.mm"
include "divsubdird.mm"
include "3eqtr3d.mm"
include "divcan3d.mm"
include "mulassd.mm"
include "divassd.mm"
include "oveq12d.mm"
include "c1.mm"
include "cneg.mm"
include "ixi.mm"
include "neg1rr.mm"
include "eqeltri.mm"
include "simpr.mm"
include "remulcl.mm"
include "cjth.mm"
include "simprd.mm"
include "rehalfcld.mm"
include "eqeltrd.mm"
include "rimul.mm"
include "syl2anc.mm"
include "subeq0d.mm"
include "eqtrd.mm"

theorem crre
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( Re ` ( A + ( _i x. B ) ) ) = A )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    #
    @4
    @4
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    @2
    @4
    cc
    wcel
    #
    @5
    @8
    wceq
    @0
    cA
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @9
    @1
    cA
    recn
    #
    @1
    ci
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @11
    ax-icn
    cB
    recn
    #
    ci
    cB
    mulcl
    #
    sylancr
    cA
    @3
    addcl
    syl2an
    #
    @4
    reval
    syl
    #
    @2
    @8
    cA
    @2
    @7
    @2
    @4
    @6
    @17
    @2
    @9
    @6
    cc
    wcel
    @17
    @4
    cjcl
    syl
    #
    addcld
    #
    halfcld
    @0
    @10
    @1
    @12
    adantr
    #
    @2
    @8
    cA
    cmin
    co
    #
    cr
    wcel
    ci
    @22
    cmul
    co
    #
    cr
    wcel
    @22
    cc0
    wceq
    @2
    @8
    cA
    @2
    @5
    @8
    cr
    @18
    @2
    @9
    @5
    cr
    wcel
    @17
    @4
    recl
    syl
    eqeltrrd
    @0
    @1
    simpl
    resubcld
    @2
    @23
    ci
    ci
    cmul
    co
    #
    cB
    cmul
    co
    #
    ci
    @4
    @6
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cr
    @2
    ci
    @3
    @26
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cmul
    co
    ci
    @3
    cmul
    co
    #
    ci
    @30
    cmul
    co
    #
    cmin
    co
    @23
    @29
    @2
    ci
    @3
    @30
    @13
    @2
    ax-icn
    a1i
    #
    @2
    @13
    @14
    @11
    ax-icn
    @1
    @14
    @0
    @15
    adantl
    #
    @16
    sylancr
    #
    @2
    @26
    @2
    @4
    @6
    @17
    @19
    subcld
    #
    halfcld
    subdid
    @2
    @22
    @31
    ci
    cmul
    @2
    @8
    c2
    cA
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    c2
    @3
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @30
    cmin
    co
    #
    @22
    @31
    @2
    @7
    @38
    cmin
    co
    #
    c2
    cdiv
    co
    @41
    @26
    cmin
    co
    #
    c2
    cdiv
    co
    @40
    @43
    @2
    @44
    @45
    c2
    cdiv
    @2
    @7
    cA
    cA
    caddc
    co
    #
    cmin
    co
    #
    @3
    @3
    caddc
    co
    #
    @26
    cmin
    co
    #
    @44
    @45
    @2
    @4
    @46
    cmin
    co
    #
    @6
    caddc
    co
    @48
    @4
    cmin
    co
    #
    @6
    caddc
    co
    @47
    @49
    @2
    @50
    @51
    @6
    caddc
    @2
    @50
    @3
    cA
    cmin
    co
    @51
    @2
    cA
    @3
    cA
    @21
    @36
    @21
    pnpcand
    @2
    @3
    cA
    @3
    @36
    @21
    @36
    pnpcan2d
    eqtr4d
    oveq1d
    @2
    @4
    @6
    @46
    @17
    @19
    @2
    cA
    cA
    @21
    @21
    addcld
    addsubd
    @2
    @48
    @4
    @6
    @2
    @3
    @3
    @36
    @36
    addcld
    @17
    @19
    subsubd
    3eqtr4d
    @2
    @38
    @46
    @7
    cmin
    @2
    cA
    @21
    2timesd
    oveq2d
    @2
    @41
    @48
    @26
    cmin
    @2
    @3
    @36
    2timesd
    oveq1d
    3eqtr4d
    oveq1d
    @2
    @7
    @38
    c2
    @20
    @2
    c2
    cc
    wcel
    #
    @10
    @38
    cc
    wcel
    2cn
    @21
    c2
    cA
    mulcl
    sylancr
    @52
    @2
    2cn
    a1i
    #
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    #
    divsubdird
    @2
    @41
    @26
    c2
    @2
    @52
    @11
    @41
    cc
    wcel
    2cn
    @36
    c2
    @3
    mulcl
    sylancr
    @37
    @53
    @54
    divsubdird
    3eqtr3d
    @2
    @39
    cA
    @8
    cmin
    @2
    cA
    c2
    @21
    @53
    @54
    divcan3d
    oveq2d
    @2
    @42
    @3
    @30
    cmin
    @2
    @3
    c2
    @36
    @53
    @54
    divcan3d
    oveq1d
    3eqtr3d
    oveq2d
    @2
    @25
    @32
    @28
    @33
    cmin
    @2
    ci
    ci
    cB
    @34
    @34
    @35
    mulassd
    @2
    ci
    @26
    c2
    @34
    @37
    @53
    @54
    divassd
    oveq12d
    3eqtr4d
    @2
    @25
    @28
    @2
    @24
    cr
    wcel
    @1
    @25
    cr
    wcel
    @24
    c1
    cneg
    cr
    ixi
    neg1rr
    eqeltri
    @0
    @1
    simpr
    @24
    cB
    remulcl
    sylancr
    @2
    @27
    @2
    @9
    @27
    cr
    wcel
    #
    @17
    @9
    @7
    cr
    wcel
    @55
    @4
    cjth
    simprd
    syl
    rehalfcld
    resubcld
    eqeltrd
    @22
    rimul
    syl2anc
    subeq0d
    eqtrd
end
