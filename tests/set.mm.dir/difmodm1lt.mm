include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "wa.mm"
include "cc0.mm"
include "simpl.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "3ad2ant1.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "wi.mm"
include "1lt2.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "3jca.mm"
include "lttr.mm"
include "syl.mm"
include "mpani.mm"
include "3imp.mm"
include "adantl.mm"
include "m1mod0mod1.mm"
include "mpbird.mm"
include "oveq12d.mm"
include "caddc.mm"
include "df-2.mm"
include "breq1i.mm"
include "biimpi.mm"
include "adantr.mm"
include "ltaddsub2d.mm"
include "mpbid.mm"
include "1m0e1.mm"
include "sylibr.mm"
include "3adant1.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "cle.mm"
include "cfz.mm"
include "zmodfz.mm"
include "3adant3.mm"
include "elfzle2.mm"
include "crp.mm"
include "nnrp.mm"
include "modcld.mm"
include "peano2rem.mm"
include "peano2zm.mm"
include "zred.mm"
include "lesub1.mm"
include "wne.mm"
include "jca.mm"
include "modge0.mm"
include "bicomd.mm"
include "notbid.mm"
include "biimpac.mm"
include "neqned.mm"
include "0red.mm"
include "ltlen.mm"
include "ltsubpos.mm"
include "resubcld.mm"
include "lelttr.mm"
include "mp2and.mm"
include "pm2.61ian.mm"

theorem difmodm1lt
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ N e. NN /\ 2 < N ) -> ( ( A mod N ) - ( ( A - 1 ) mod N ) ) < ( N - 1 ) )

  proof
    cA
    cN
    cmo
    co
    #
    c1
    wceq
    #
    cA
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    c2
    cN
    clt
    wbr
    #
    w3a
    #
    @0
    cA
    c1
    cmin
    co
    #
    cN
    cmo
    co
    #
    cmin
    co
    #
    cN
    c1
    cmin
    co
    #
    clt
    wbr
    #
    @1
    @5
    wa
    #
    @8
    c1
    cc0
    cmin
    co
    #
    @9
    clt
    @11
    @0
    c1
    @7
    cc0
    cmin
    @1
    @5
    simpl
    #
    @11
    @7
    cc0
    wceq
    #
    @1
    @13
    @11
    cA
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    w3a
    #
    @14
    @1
    wb
    #
    @5
    @18
    @1
    @5
    @15
    @16
    @17
    @2
    @3
    @15
    @4
    cA
    zre
    3ad2ant1
    #
    @3
    @2
    @16
    @4
    cN
    nnre
    #
    3ad2ant2
    @2
    @3
    @4
    @17
    @3
    @4
    @17
    wi
    wi
    @2
    @3
    c1
    c2
    clt
    wbr
    #
    @4
    @17
    1lt2
    @3
    c1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @16
    w3a
    @22
    @4
    wa
    @17
    wi
    @3
    @23
    @24
    @16
    @3
    1red
    @24
    @3
    2re
    a1i
    @21
    3jca
    c1
    c2
    cN
    lttr
    syl
    mpani
    a1i
    3imp
    3jca
    #
    adantl
    cA
    cN
    m1mod0mod1
    #
    syl
    mpbird
    oveq12d
    @5
    @12
    @9
    clt
    wbr
    #
    @1
    @3
    @4
    @27
    @2
    @3
    @4
    wa
    #
    c1
    @9
    clt
    wbr
    #
    @27
    @28
    c1
    c1
    caddc
    co
    #
    cN
    clt
    wbr
    #
    @29
    @4
    @31
    @3
    @4
    @31
    c2
    @30
    cN
    clt
    df-2
    breq1i
    biimpi
    adantl
    @28
    c1
    c1
    cN
    @28
    1red
    #
    @32
    @3
    @16
    @4
    @21
    adantr
    ltaddsub2d
    mpbid
    @12
    c1
    @9
    clt
    1m0e1
    breq1i
    sylibr
    3adant1
    adantl
    eqbrtrd
    @1
    wn
    #
    @5
    wa
    #
    @8
    @9
    @7
    cmin
    co
    #
    cle
    wbr
    #
    @35
    @9
    clt
    wbr
    #
    @10
    @34
    @0
    @9
    cle
    wbr
    #
    @36
    @5
    @38
    @33
    @5
    @0
    cc0
    @9
    cfz
    co
    wcel
    #
    @38
    @2
    @3
    @39
    @4
    cA
    cN
    zmodfz
    3adant3
    @0
    cc0
    @9
    elfzle2
    syl
    adantl
    @34
    @0
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    w3a
    #
    @38
    @36
    wb
    @5
    @43
    @33
    @5
    @40
    @41
    @42
    @5
    cA
    cN
    @20
    @3
    @2
    cN
    crp
    wcel
    #
    @4
    cN
    nnrp
    3ad2ant2
    #
    modcld
    #
    @3
    @2
    @41
    @4
    @3
    @16
    @41
    @21
    cN
    peano2rem
    syl
    3ad2ant2
    #
    @5
    @6
    cN
    @2
    @3
    @6
    cr
    wcel
    #
    @4
    @2
    @6
    cA
    peano2zm
    zred
    3ad2ant1
    #
    @45
    modcld
    #
    3jca
    adantl
    @0
    @9
    @7
    lesub1
    syl
    mpbid
    @34
    cc0
    @7
    clt
    wbr
    #
    @37
    @34
    @51
    cc0
    @7
    cle
    wbr
    #
    @7
    cc0
    wne
    #
    wa
    #
    @34
    @52
    @53
    @34
    @48
    @44
    wa
    #
    @52
    @5
    @55
    @33
    @5
    @48
    @44
    @49
    @45
    jca
    adantl
    @6
    cN
    modge0
    syl
    @34
    @7
    cc0
    @5
    @33
    @14
    wn
    @5
    @1
    @14
    @5
    @14
    @1
    @5
    @18
    @19
    @25
    @26
    syl
    bicomd
    notbid
    biimpac
    neqned
    jca
    @34
    cc0
    cr
    wcel
    #
    @42
    wa
    #
    @51
    @54
    wb
    @5
    @57
    @33
    @5
    @56
    @42
    @5
    0red
    @50
    jca
    adantl
    cc0
    @7
    ltlen
    syl
    mpbird
    @34
    @42
    @41
    wa
    #
    @51
    @37
    wb
    @5
    @58
    @33
    @5
    @42
    @41
    @50
    @47
    jca
    adantl
    @7
    @9
    ltsubpos
    syl
    mpbid
    @34
    @8
    cr
    wcel
    #
    @35
    cr
    wcel
    #
    @41
    w3a
    #
    @36
    @37
    wa
    @10
    wi
    @5
    @61
    @33
    @5
    @59
    @60
    @41
    @5
    @0
    @7
    @46
    @50
    resubcld
    @5
    @9
    @7
    @47
    @50
    resubcld
    @47
    3jca
    adantl
    @8
    @35
    @9
    lelttr
    syl
    mp2and
    pm2.61ian
end
