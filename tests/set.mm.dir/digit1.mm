include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "cmo.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "digit2.mm"
include "3coml.mm"
include "3expa.mm"
include "oveq1d.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cn0.mm"
include "nnre.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "syl2an.mm"
include "remulcl.mm"
include "sylan.mm"
include "reflcl.mm"
include "syl.mm"
include "nnrp.mm"
include "ad2antrr.mm"
include "modcld.mm"
include "nnexpcl.mm"
include "sylan2.mm"
include "nnrpd.mm"
include "adantr.mm"
include "modge0.mm"
include "syl2anc.mm"
include "modlt.mm"
include "cc.mm"
include "nncn.mm"
include "exp1.mm"
include "cuz.mm"
include "nnge1.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "leexp2a.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "modid.mm"
include "syl22anc.mm"
include "simpll.mm"
include "nnm1nn0.mm"
include "modmulnn.mm"
include "expm1t.mm"
include "expcl.mm"
include "simpl.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "recn.mm"
include "adantl.mm"
include "mulassd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "modsubdir.mm"
include "mpbid.mm"
include "3eqtr3d.mm"
include "3impa.mm"
include "3comr.mm"

theorem digit1
  let cA: class A
  let cB: class B
  let cK: class K


  assert |- ( ( A e. RR /\ B e. NN /\ K e. NN ) -> ( ( |_ ` ( ( B ^ K ) x. A ) ) mod B ) = ( ( ( |_ ` ( ( B ^ K ) x. A ) ) mod ( B ^ K ) ) - ( ( B x. ( |_ ` ( ( B ^ ( K - 1 ) ) x. A ) ) ) mod ( B ^ K ) ) ) )

  proof
    cB
    cn
    wcel
    #
    cK
    cn
    wcel
    #
    cA
    cr
    wcel
    #
    cB
    cK
    cexp
    co
    #
    cA
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    @5
    @3
    cmo
    co
    #
    cB
    cB
    cK
    c1
    cmin
    co
    #
    cexp
    co
    #
    cA
    cmul
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    @3
    cmo
    co
    #
    cmin
    co
    #
    wceq
    #
    @0
    @1
    @2
    @15
    @0
    @1
    wa
    #
    @2
    wa
    #
    @6
    @3
    cmo
    co
    #
    @5
    @12
    cmin
    co
    #
    @3
    cmo
    co
    #
    @6
    @14
    @17
    @6
    @19
    @3
    cmo
    @0
    @1
    @2
    @6
    @19
    wceq
    #
    @2
    @0
    @1
    @21
    cA
    cB
    cK
    digit2
    3coml
    3expa
    oveq1d
    @17
    @6
    cr
    wcel
    @3
    crp
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    @3
    clt
    wbr
    @18
    @6
    wceq
    @17
    @5
    cB
    @17
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @16
    @3
    cr
    wcel
    #
    @2
    @24
    @0
    cB
    cr
    wcel
    #
    cK
    cn0
    wcel
    #
    @26
    @1
    cB
    nnre
    #
    cK
    nnnn0
    #
    cB
    cK
    reexpcl
    syl2an
    #
    @3
    cA
    remulcl
    sylan
    @4
    reflcl
    syl
    #
    @0
    cB
    crp
    wcel
    #
    @1
    @2
    cB
    nnrp
    ad2antrr
    #
    modcld
    #
    @16
    @22
    @2
    @16
    @3
    @1
    @0
    @28
    @3
    cn
    wcel
    @30
    cB
    cK
    nnexpcl
    sylan2
    nnrpd
    adantr
    #
    @17
    @25
    @33
    @23
    @32
    @34
    @5
    cB
    modge0
    syl2anc
    @17
    @6
    cB
    @3
    @35
    @0
    @27
    @1
    @2
    @29
    ad2antrr
    #
    @16
    @26
    @2
    @31
    adantr
    @17
    @25
    @33
    @6
    cB
    clt
    wbr
    @32
    @34
    @5
    cB
    modlt
    syl2anc
    @16
    cB
    @3
    cle
    wbr
    @2
    @16
    cB
    c1
    cexp
    co
    #
    cB
    @3
    cle
    @0
    @38
    cB
    wceq
    #
    @1
    @0
    cB
    cc
    wcel
    #
    @39
    cB
    nncn
    #
    cB
    exp1
    syl
    adantr
    @16
    @27
    c1
    cB
    cle
    wbr
    #
    cK
    c1
    cuz
    cfv
    #
    wcel
    @38
    @3
    cle
    wbr
    @0
    @27
    @1
    @29
    adantr
    @0
    @42
    @1
    cB
    nnge1
    adantr
    @16
    cK
    cn
    @43
    @0
    @1
    simpr
    nnuz
    syl6eleq
    cB
    c1
    cK
    leexp2a
    syl3anc
    eqbrtrrd
    adantr
    ltletrd
    @6
    @3
    modid
    syl22anc
    @17
    @13
    @7
    cle
    wbr
    #
    @20
    @14
    wceq
    #
    @17
    @12
    cB
    @9
    cmul
    co
    #
    cmo
    co
    #
    cB
    @10
    cmul
    co
    #
    cfl
    cfv
    #
    @46
    cmo
    co
    #
    @13
    @7
    cle
    @17
    @0
    @10
    cr
    wcel
    #
    @9
    cn
    wcel
    #
    @47
    @50
    cle
    wbr
    @0
    @1
    @2
    simpll
    @16
    @9
    cr
    wcel
    #
    @2
    @51
    @0
    @27
    @8
    cn0
    wcel
    #
    @53
    @1
    @29
    cK
    nnm1nn0
    #
    cB
    @8
    reexpcl
    syl2an
    @9
    cA
    remulcl
    sylan
    #
    @16
    @52
    @2
    @1
    @0
    @54
    @52
    @55
    cB
    @8
    nnexpcl
    sylan2
    adantr
    @10
    @9
    cB
    modmulnn
    syl3anc
    @17
    @3
    @46
    @12
    cmo
    @16
    @3
    @46
    wceq
    #
    @2
    @0
    @40
    @1
    @57
    @41
    @40
    @1
    wa
    #
    @3
    @9
    cB
    cmul
    co
    @46
    cB
    cK
    expm1t
    @58
    @9
    cB
    @1
    @40
    @54
    @9
    cc
    wcel
    #
    @55
    cB
    @8
    expcl
    #
    sylan2
    @40
    @1
    simpl
    mulcomd
    eqtrd
    sylan
    adantr
    #
    oveq2d
    @17
    @5
    @49
    @3
    @46
    cmo
    @17
    @4
    @48
    cfl
    @17
    @4
    @46
    cA
    cmul
    co
    @48
    @17
    @3
    @46
    cA
    cmul
    @61
    oveq1d
    @17
    cB
    @9
    cA
    @0
    @40
    @1
    @2
    @41
    ad2antrr
    @16
    @59
    @2
    @0
    @40
    @54
    @59
    @1
    @41
    @55
    @60
    syl2an
    adantr
    @2
    cA
    cc
    wcel
    @16
    cA
    recn
    adantl
    mulassd
    eqtrd
    fveq2d
    @61
    oveq12d
    3brtr4d
    @17
    @25
    @12
    cr
    wcel
    #
    @22
    @44
    @45
    wb
    @32
    @17
    @27
    @11
    cr
    wcel
    #
    @62
    @37
    @17
    @51
    @63
    @56
    @10
    reflcl
    syl
    cB
    @11
    remulcl
    syl2anc
    @36
    @5
    @12
    @3
    modsubdir
    syl3anc
    mpbid
    3eqtr3d
    3impa
    3comr
end
