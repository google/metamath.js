include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c3.mm"
include "c5.mm"
include "cpr.mm"
include "cmul.mm"
include "cneg.mm"
include "c1.mm"
include "c7.mm"
include "wceq.mm"
include "wo.mm"
include "ovex.mm"
include "elpr.mm"
include "anbi12i.mm"
include "simpll.mm"
include "3z.mm"
include "a1i.mm"
include "simplr.mm"
include "crp.mm"
include "8re.mm"
include "8pos.mm"
include "elrpii.mm"
include "simprl.mm"
include "lgsdir2lem1.mm"
include "simpri.mm"
include "simpli.mm"
include "syl6eqr.mm"
include "simprr.mm"
include "modmul12d.mm"
include "orcd.mm"
include "ex.mm"
include "znegcl.mm"
include "mp1i.mm"
include "3cn.mm"
include "mulneg1i.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "olcd.mm"
include "mulneg2i.mm"
include "mul2negi.mm"
include "ccased.mm"
include "syl5bi.mm"
include "imp.mm"
include "sylibr.mm"
include "caddc.mm"
include "c9.mm"
include "df-9.mm"
include "8cn.mm"
include "ax-1cn.mm"
include "addcomi.mm"
include "eqtri.mm"
include "3t3e9.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"
include "cr.mm"
include "1re.mm"
include "1z.mm"
include "modcyc.mm"
include "mp3an.mm"
include "wtru.mm"
include "3nn.mm"
include "nnmulcli.mm"
include "nnzi.mm"
include "eqidd.mm"
include "trud.mm"
include "mulcli.mm"
include "mulm1i.mm"
include "3eqtr3i.mm"
include "preq12i.mm"
include "syl6eleq.mm"

theorem lgsdir2lem5
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


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( ( A mod 8 ) e. { 3 , 5 } /\ ( B mod 8 ) e. { 3 , 5 } ) ) -> ( ( A x. B ) mod 8 ) e. { 1 , 7 } )

  proof
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
    cA
    c8
    cmo
    co
    #
    c3
    c5
    cpr
    #
    wcel
    #
    cB
    c8
    cmo
    co
    #
    @4
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    c8
    cmo
    co
    #
    c3
    c3
    cmul
    co
    #
    c8
    cmo
    co
    #
    @12
    cneg
    #
    c8
    cmo
    co
    #
    cpr
    #
    c1
    c7
    cpr
    @9
    @11
    @13
    wceq
    #
    @11
    @15
    wceq
    #
    wo
    #
    @11
    @16
    wcel
    @2
    @8
    @19
    @8
    @3
    c3
    wceq
    #
    @3
    c5
    wceq
    #
    wo
    #
    @6
    c3
    wceq
    #
    @6
    c5
    wceq
    #
    wo
    #
    wa
    @2
    @19
    @5
    @22
    @7
    @25
    @3
    c3
    c5
    cA
    c8
    cmo
    ovex
    elpr
    @6
    c3
    c5
    cB
    c8
    cmo
    ovex
    elpr
    anbi12i
    @2
    @20
    @23
    @21
    @24
    @19
    @2
    @20
    @23
    wa
    #
    @19
    @2
    @26
    wa
    #
    @17
    @18
    @27
    cA
    c3
    cB
    c3
    c8
    @0
    @1
    @26
    simpll
    c3
    cz
    wcel
    #
    @27
    3z
    a1i
    #
    @0
    @1
    @26
    simplr
    @29
    c8
    crp
    wcel
    #
    @27
    c8
    8re
    8pos
    elrpii
    #
    a1i
    @27
    @3
    c3
    c3
    c8
    cmo
    co
    #
    @2
    @20
    @23
    simprl
    @32
    c3
    wceq
    #
    c3
    cneg
    #
    c8
    cmo
    co
    #
    c5
    wceq
    #
    c1
    c8
    cmo
    co
    #
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
    wa
    #
    @33
    @36
    wa
    #
    lgsdir2lem1
    simpri
    #
    simpli
    #
    syl6eqr
    @27
    @6
    c3
    @32
    @2
    @20
    @23
    simprr
    @45
    syl6eqr
    modmul12d
    orcd
    ex
    @2
    @21
    @23
    wa
    #
    @19
    @2
    @46
    wa
    #
    @18
    @17
    @47
    @11
    @34
    c3
    cmul
    co
    #
    c8
    cmo
    co
    @15
    @47
    cA
    @34
    cB
    c3
    c8
    @0
    @1
    @46
    simpll
    @28
    @34
    cz
    wcel
    #
    @47
    3z
    c3
    znegcl
    #
    mp1i
    @0
    @1
    @46
    simplr
    @28
    @47
    3z
    a1i
    @30
    @47
    @31
    a1i
    @47
    @3
    c5
    @35
    @2
    @21
    @23
    simprl
    @33
    @36
    @44
    simpri
    #
    syl6eqr
    @47
    @6
    c3
    @32
    @2
    @21
    @23
    simprr
    @45
    syl6eqr
    modmul12d
    @48
    @14
    c8
    cmo
    c3
    c3
    3cn
    3cn
    mulneg1i
    oveq1i
    syl6eq
    olcd
    ex
    @2
    @20
    @24
    wa
    #
    @19
    @2
    @52
    wa
    #
    @18
    @17
    @53
    @11
    c3
    @34
    cmul
    co
    #
    c8
    cmo
    co
    @15
    @53
    cA
    c3
    cB
    @34
    c8
    @0
    @1
    @52
    simpll
    @28
    @53
    3z
    a1i
    @0
    @1
    @52
    simplr
    @28
    @49
    @53
    3z
    @50
    mp1i
    @30
    @53
    @31
    a1i
    @53
    @3
    c3
    @32
    @2
    @20
    @24
    simprl
    @45
    syl6eqr
    @53
    @6
    c5
    @35
    @2
    @20
    @24
    simprr
    @51
    syl6eqr
    modmul12d
    @54
    @14
    c8
    cmo
    c3
    c3
    3cn
    3cn
    mulneg2i
    oveq1i
    syl6eq
    olcd
    ex
    @2
    @21
    @24
    wa
    #
    @19
    @2
    @55
    wa
    #
    @17
    @18
    @56
    @11
    @34
    @34
    cmul
    co
    #
    c8
    cmo
    co
    @13
    @56
    cA
    @34
    cB
    @34
    c8
    @0
    @1
    @55
    simpll
    @28
    @49
    @56
    3z
    @50
    mp1i
    #
    @0
    @1
    @55
    simplr
    @58
    @30
    @56
    @31
    a1i
    @56
    @3
    c5
    @35
    @2
    @21
    @24
    simprl
    @51
    syl6eqr
    @56
    @6
    c5
    @35
    @2
    @21
    @24
    simprr
    @51
    syl6eqr
    modmul12d
    @57
    @12
    c8
    cmo
    c3
    c3
    3cn
    3cn
    mul2negi
    oveq1i
    syl6eq
    orcd
    ex
    ccased
    syl5bi
    imp
    @11
    @13
    @15
    @10
    c8
    cmo
    ovex
    elpr
    sylibr
    @13
    c1
    @15
    c7
    @13
    @37
    c1
    @13
    c1
    c1
    c8
    cmul
    co
    #
    caddc
    co
    #
    c8
    cmo
    co
    #
    @37
    @12
    @60
    c8
    cmo
    c9
    c1
    c8
    caddc
    co
    #
    @12
    @60
    c9
    c8
    c1
    caddc
    co
    @62
    df-9
    c8
    c1
    8cn
    ax-1cn
    addcomi
    eqtri
    3t3e9
    @59
    c8
    c1
    caddc
    c8
    8cn
    mulid2i
    oveq2i
    3eqtr4i
    oveq1i
    c1
    cr
    wcel
    @30
    c1
    cz
    wcel
    #
    @61
    @37
    wceq
    1re
    @31
    1z
    c1
    c8
    c1
    modcyc
    mp3an
    eqtri
    #
    @38
    @41
    @42
    @43
    lgsdir2lem1
    simpli
    #
    simpli
    eqtri
    @15
    @40
    c7
    @39
    @12
    cmul
    co
    #
    c8
    cmo
    co
    #
    @39
    c1
    cmul
    co
    #
    c8
    cmo
    co
    #
    @15
    @40
    @67
    @69
    wceq
    wtru
    @39
    @39
    @12
    c1
    c8
    @63
    @39
    cz
    wcel
    wtru
    1z
    c1
    znegcl
    mp1i
    #
    @70
    @12
    cz
    wcel
    wtru
    @12
    c3
    c3
    3nn
    3nn
    nnmulcli
    nnzi
    a1i
    @63
    wtru
    1z
    a1i
    @30
    wtru
    @31
    a1i
    wtru
    @40
    eqidd
    @13
    @37
    wceq
    wtru
    @64
    a1i
    modmul12d
    trud
    @66
    @14
    c8
    cmo
    @12
    c3
    c3
    3cn
    3cn
    mulcli
    mulm1i
    oveq1i
    @68
    @39
    c8
    cmo
    c1
    ax-1cn
    mulm1i
    oveq1i
    3eqtr3i
    @38
    @41
    @65
    simpri
    eqtri
    preq12i
    syl6eleq
end
