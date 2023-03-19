include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "cmul.mm"
include "wb.mm"
include "ovex.mm"
include "elpr.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "ad2antrr.mm"
include "1red.mm"
include "simplr.mm"
include "8re.mm"
include "8pos.mm"
include "elrpii.mm"
include "a1i.mm"
include "simpr.mm"
include "cneg.mm"
include "c3.mm"
include "c5.mm"
include "lgsdir2lem1.mm"
include "simpli.mm"
include "syl6eqr.mm"
include "modmul1.mm"
include "syl221anc.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antlr.mm"
include "mulid2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "neg1rr.mm"
include "simpri.mm"
include "mulm1d.mm"
include "wi.mm"
include "znegcl.mm"
include "cv.mm"
include "oveq1.mm"
include "negeq.mm"
include "imbi12d.mm"
include "neg1cn.mm"
include "mulcom.mm"
include "mpan2.mm"
include "mulm1.mm"
include "syl.mm"
include "adantr.mm"
include "neg1z.mm"
include "eqtr3d.mm"
include "mulid2i.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "ex.mm"
include "neg1mulneg1e1.mm"
include "orim12d.mm"
include "orcom.mm"
include "bitri.mm"
include "3imtr4g.mm"
include "vtoclga.mm"
include "negnegd.mm"
include "sylibd.mm"
include "impbid.mm"
include "bitrd.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem lgsdir2lem4
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p
  let cN: class N


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( A mod 8 ) e. { 1 , 7 } ) -> ( ( ( A x. B ) mod 8 ) e. { 1 , 7 } <-> ( B mod 8 ) e. { 1 , 7 } ) )

  proof
    cA
    c8
    cmo
    co
    #
    c1
    c7
    cpr
    #
    wcel
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    @0
    c1
    wceq
    #
    @0
    c7
    wceq
    #
    wo
    cA
    cB
    cmul
    co
    c8
    cmo
    co
    #
    @1
    wcel
    #
    cB
    c8
    cmo
    co
    #
    @1
    wcel
    #
    wb
    #
    @0
    c1
    c7
    cA
    c8
    cmo
    ovex
    elpr
    @4
    @5
    @11
    @6
    @4
    @5
    wa
    #
    @7
    @9
    @1
    @12
    @7
    c1
    cB
    cmul
    co
    #
    c8
    cmo
    co
    #
    @9
    @12
    cA
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @3
    c8
    crp
    wcel
    #
    @0
    c1
    c8
    cmo
    co
    #
    wceq
    @7
    @14
    wceq
    @2
    @15
    @3
    @5
    cA
    zre
    #
    ad2antrr
    @12
    1red
    @2
    @3
    @5
    simplr
    @17
    @12
    c8
    8re
    8pos
    elrpii
    #
    a1i
    @12
    @0
    c1
    @18
    @4
    @5
    simpr
    @18
    c1
    wceq
    #
    c1
    cneg
    #
    c8
    cmo
    co
    #
    c7
    wceq
    #
    @21
    @24
    wa
    c3
    c8
    cmo
    co
    c3
    wceq
    c3
    cneg
    c8
    cmo
    co
    c5
    wceq
    wa
    lgsdir2lem1
    simpli
    #
    simpli
    #
    syl6eqr
    cA
    c1
    cB
    c8
    modmul1
    syl221anc
    @12
    @13
    cB
    c8
    cmo
    @12
    cB
    @3
    cB
    cc
    wcel
    #
    @2
    @5
    cB
    zcn
    #
    ad2antlr
    mulid2d
    oveq1d
    eqtrd
    eleq1d
    @4
    @6
    wa
    #
    @8
    cB
    cneg
    #
    c8
    cmo
    co
    #
    @1
    wcel
    #
    @10
    @29
    @7
    @31
    @1
    @29
    @7
    @22
    cB
    cmul
    co
    #
    c8
    cmo
    co
    #
    @31
    @29
    @15
    @22
    cr
    wcel
    #
    @3
    @17
    @0
    @23
    wceq
    @7
    @34
    wceq
    @2
    @15
    @3
    @6
    @19
    ad2antrr
    @35
    @29
    neg1rr
    a1i
    @2
    @3
    @6
    simplr
    @17
    @29
    @20
    a1i
    @29
    @0
    c7
    @23
    @4
    @6
    simpr
    @21
    @24
    @25
    simpri
    #
    syl6eqr
    cA
    @22
    cB
    c8
    modmul1
    syl221anc
    @29
    @33
    @30
    c8
    cmo
    @29
    cB
    @3
    @27
    @2
    @6
    @28
    ad2antlr
    mulm1d
    oveq1d
    eqtrd
    eleq1d
    @3
    @32
    @10
    wb
    @2
    @6
    @3
    @32
    @10
    @3
    @32
    @30
    cneg
    #
    c8
    cmo
    co
    #
    @1
    wcel
    #
    @10
    @3
    @30
    cz
    wcel
    @32
    @39
    wi
    #
    cB
    znegcl
    vx
    cv
    #
    c8
    cmo
    co
    #
    @1
    wcel
    #
    @41
    cneg
    #
    c8
    cmo
    co
    #
    @1
    wcel
    #
    wi
    #
    @40
    vx
    @30
    cz
    @41
    @30
    wceq
    #
    @43
    @32
    @46
    @39
    @48
    @42
    @31
    @1
    @41
    @30
    c8
    cmo
    oveq1
    eleq1d
    @48
    @45
    @38
    @1
    @48
    @44
    @37
    c8
    cmo
    @41
    @30
    negeq
    oveq1d
    eleq1d
    imbi12d
    @41
    cz
    wcel
    #
    @42
    c1
    wceq
    #
    @42
    c7
    wceq
    #
    wo
    @45
    c7
    wceq
    #
    @45
    c1
    wceq
    #
    wo
    #
    @43
    @46
    @49
    @50
    @52
    @51
    @53
    @49
    @50
    @52
    @49
    @50
    wa
    #
    @45
    c1
    @22
    cmul
    co
    #
    c8
    cmo
    co
    #
    c7
    @55
    @41
    @22
    cmul
    co
    #
    c8
    cmo
    co
    #
    @45
    @57
    @55
    @58
    @44
    c8
    cmo
    @49
    @58
    @44
    wceq
    #
    @50
    @49
    @41
    cc
    wcel
    #
    @60
    @41
    zcn
    @61
    @58
    @22
    @41
    cmul
    co
    #
    @44
    @61
    @22
    cc
    wcel
    @58
    @62
    wceq
    neg1cn
    @41
    @22
    mulcom
    mpan2
    @41
    mulm1
    eqtrd
    syl
    #
    adantr
    oveq1d
    @55
    @41
    cr
    wcel
    #
    @16
    @22
    cz
    wcel
    #
    @17
    @42
    @18
    wceq
    @59
    @57
    wceq
    @49
    @64
    @50
    @41
    zre
    #
    adantr
    @55
    1red
    @65
    @55
    neg1z
    a1i
    @17
    @55
    @20
    a1i
    @55
    @42
    c1
    @18
    @49
    @50
    simpr
    @26
    syl6eqr
    @41
    c1
    @22
    c8
    modmul1
    syl221anc
    eqtr3d
    @57
    @23
    c7
    @56
    @22
    c8
    cmo
    @22
    neg1cn
    mulid2i
    oveq1i
    @36
    eqtri
    syl6eq
    ex
    @49
    @51
    @53
    @49
    @51
    wa
    #
    @45
    @22
    @22
    cmul
    co
    #
    c8
    cmo
    co
    #
    c1
    @67
    @59
    @45
    @69
    @67
    @58
    @44
    c8
    cmo
    @49
    @60
    @51
    @63
    adantr
    oveq1d
    @67
    @64
    @35
    @65
    @17
    @42
    @23
    wceq
    @59
    @69
    wceq
    @49
    @64
    @51
    @66
    adantr
    @35
    @67
    neg1rr
    a1i
    @65
    @67
    neg1z
    a1i
    @17
    @67
    @20
    a1i
    @67
    @42
    c7
    @23
    @49
    @51
    simpr
    @36
    syl6eqr
    @41
    @22
    @22
    c8
    modmul1
    syl221anc
    eqtr3d
    @69
    @18
    c1
    @68
    c1
    c8
    cmo
    neg1mulneg1e1
    oveq1i
    @26
    eqtri
    syl6eq
    ex
    orim12d
    @42
    c1
    c7
    @41
    c8
    cmo
    ovex
    elpr
    @46
    @53
    @52
    wo
    @54
    @45
    c1
    c7
    @44
    c8
    cmo
    ovex
    elpr
    @53
    @52
    orcom
    bitri
    3imtr4g
    #
    vtoclga
    syl
    @3
    @38
    @9
    @1
    @3
    @37
    cB
    c8
    cmo
    @3
    cB
    @28
    negnegd
    oveq1d
    eleq1d
    sylibd
    @47
    @10
    @32
    wi
    vx
    cB
    cz
    @41
    cB
    wceq
    #
    @43
    @10
    @46
    @32
    @71
    @42
    @9
    @1
    @41
    cB
    c8
    cmo
    oveq1
    eleq1d
    @71
    @45
    @31
    @1
    @71
    @44
    @30
    c8
    cmo
    @41
    cB
    negeq
    oveq1d
    eleq1d
    imbi12d
    @70
    vtoclga
    impbid
    ad2antlr
    bitrd
    jaodan
    sylan2b
end
