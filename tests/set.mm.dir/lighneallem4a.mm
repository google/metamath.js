include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c3.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "wceq.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "eluzelre.mm"
include "peano2re.mm"
include "syl.mm"
include "remulcld.mm"
include "adantr.mm"
include "cn0.mm"
include "eluzge2nn0.mm"
include "eluzge3nn.mm"
include "nnnn0d.mm"
include "adantl.mm"
include "nn0expcld.mm"
include "nn0red.mm"
include "1red.mm"
include "eluz2nn.mm"
include "nnge1d.mm"
include "leadd2dd.mm"
include "eluzelcn.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "3jca.mm"
include "lemul2.mm"
include "mpbid.mm"
include "cc.mm"
include "2cn.mm"
include "mulassd.mm"
include "cmin.mm"
include "c4.mm"
include "sq2.mm"
include "4re.mm"
include "eqeltri.mm"
include "nn0sqcl.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "2nn0.mm"
include "0le2.mm"
include "eluzle.mm"
include "leexp1a.mm"
include "syl12anc.mm"
include "2p1e3.mm"
include "syl5eqbr.mm"
include "leaddsub.mm"
include "mp3an2i.mm"
include "cz.mm"
include "2z.mm"
include "eluzelz.mm"
include "peano2zm.mm"
include "eluz2gt1.mm"
include "leexp2d.mm"
include "letrd.mm"
include "sqvali.mm"
include "eqcomi.mm"
include "wne.mm"
include "eluz2n0.mm"
include "expm1d.mm"
include "eqcomd.mm"
include "3brtr4d.mm"
include "remulcli.mm"
include "nngt0d.mm"
include "jca.mm"
include "lemuldiv.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"
include "lep1d.mm"
include "nnnn0.mm"
include "nn0p1gt0.mm"
include "3syl.mm"
include "3adant3.mm"
include "breq2.mm"
include "3ad2ant3.mm"

theorem lighneallem4a
  let cA: class A
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ( ZZ>= ` 3 ) /\ S = ( ( ( A ^ M ) + 1 ) / ( A + 1 ) ) ) -> 2 <_ S )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cM
    c3
    cuz
    cfv
    wcel
    #
    cS
    cA
    cM
    cexp
    co
    #
    c1
    caddc
    co
    #
    cA
    c1
    caddc
    co
    #
    cdiv
    co
    #
    wceq
    #
    w3a
    c2
    cS
    cle
    wbr
    #
    c2
    @5
    cle
    wbr
    #
    @0
    @1
    @8
    @6
    @0
    @1
    wa
    #
    c2
    @4
    cmul
    co
    #
    @3
    cle
    wbr
    #
    @8
    @9
    @10
    @2
    @3
    @0
    @10
    cr
    wcel
    @1
    @0
    c2
    @4
    c2
    cr
    wcel
    #
    @0
    2re
    a1i
    #
    @0
    cA
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    c2
    cA
    eluzelre
    #
    cA
    peano2re
    syl
    #
    remulcld
    adantr
    #
    @9
    @2
    @9
    cA
    cM
    @0
    cA
    cn0
    wcel
    #
    @1
    cA
    eluzge2nn0
    #
    adantr
    #
    @1
    cM
    cn0
    wcel
    @0
    @1
    cM
    cM
    eluzge3nn
    #
    nnnn0d
    adantl
    nn0expcld
    nn0red
    #
    @9
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @23
    @2
    peano2re
    syl
    #
    @9
    @10
    c2
    c2
    cA
    cmul
    co
    #
    cmul
    co
    #
    @2
    @18
    @0
    @28
    cr
    wcel
    @1
    @0
    c2
    @27
    @13
    @0
    c2
    cA
    @13
    @16
    remulcld
    #
    remulcld
    adantr
    @23
    @9
    @4
    @27
    cle
    wbr
    #
    @10
    @28
    cle
    wbr
    #
    @0
    @30
    @1
    @0
    @4
    cA
    cA
    caddc
    co
    @27
    cle
    @0
    c1
    cA
    cA
    @0
    1red
    @16
    @16
    @0
    cA
    cA
    eluz2nn
    #
    nnge1d
    leadd2dd
    @0
    cA
    c2
    cA
    eluzelcn
    #
    2timesd
    breqtrrd
    adantr
    @9
    @15
    @27
    cr
    wcel
    #
    @12
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    w3a
    #
    @30
    @31
    wb
    @0
    @37
    @1
    @0
    @15
    @34
    @36
    @17
    @29
    @36
    @0
    @12
    @35
    2re
    2pos
    pm3.2i
    a1i
    3jca
    adantr
    @4
    @27
    c2
    lemul2
    syl
    mpbid
    @9
    c2
    c2
    cmul
    co
    #
    cA
    cmul
    co
    #
    @28
    @2
    cle
    @9
    c2
    c2
    cA
    c2
    cc
    wcel
    @9
    2cn
    a1i
    #
    @40
    @0
    cA
    cc
    wcel
    @1
    @33
    adantr
    #
    mulassd
    @9
    @39
    @2
    cle
    wbr
    #
    @38
    @2
    cA
    cdiv
    co
    #
    cle
    wbr
    #
    @9
    c2
    c2
    cexp
    co
    #
    cA
    cM
    c1
    cmin
    co
    #
    cexp
    co
    #
    @38
    @43
    cle
    @9
    @45
    cA
    c2
    cexp
    co
    #
    @47
    @45
    cr
    wcel
    @9
    @45
    c4
    cr
    sq2
    4re
    eqeltri
    a1i
    @0
    @48
    cr
    wcel
    @1
    @0
    @48
    @0
    @19
    @48
    cn0
    wcel
    @20
    cA
    nn0sqcl
    syl
    nn0red
    adantr
    @9
    @47
    @9
    cA
    @46
    @21
    @1
    @46
    cn0
    wcel
    #
    @0
    @1
    cM
    cn
    wcel
    @49
    @22
    cM
    nnm1nn0
    syl
    adantl
    nn0expcld
    nn0red
    @9
    @12
    @14
    c2
    cn0
    wcel
    #
    w3a
    #
    cc0
    c2
    cle
    wbr
    #
    c2
    cA
    cle
    wbr
    #
    @45
    @48
    cle
    wbr
    @0
    @51
    @1
    @0
    @12
    @14
    @50
    @13
    @16
    @50
    @0
    2nn0
    a1i
    3jca
    adantr
    @52
    @9
    0le2
    a1i
    @0
    @53
    @1
    c2
    cA
    eluzle
    adantr
    c2
    cA
    c2
    leexp1a
    syl12anc
    @9
    c2
    @46
    cle
    wbr
    #
    @48
    @47
    cle
    wbr
    @1
    @54
    @0
    @1
    c2
    c1
    caddc
    co
    #
    cM
    cle
    wbr
    #
    @54
    @1
    @55
    c3
    cM
    cle
    2p1e3
    c3
    cM
    eluzle
    syl5eqbr
    @12
    @1
    c1
    cr
    wcel
    cM
    cr
    wcel
    @56
    @54
    wb
    2re
    @1
    1red
    c3
    cM
    eluzelre
    c2
    c1
    cM
    leaddsub
    mp3an2i
    mpbid
    adantl
    @9
    cA
    c2
    @46
    @0
    @14
    @1
    @16
    adantr
    c2
    cz
    wcel
    @9
    2z
    a1i
    @1
    @46
    cz
    wcel
    #
    @0
    @1
    cM
    cz
    wcel
    #
    @57
    c3
    cM
    eluzelz
    #
    cM
    peano2zm
    syl
    adantl
    @0
    c1
    cA
    clt
    wbr
    @1
    cA
    eluz2gt1
    adantr
    leexp2d
    mpbid
    letrd
    @38
    @45
    wceq
    @9
    @45
    @38
    c2
    2cn
    sqvali
    eqcomi
    a1i
    @9
    @47
    @43
    @9
    cA
    cM
    @41
    @0
    cA
    cc0
    wne
    @1
    cA
    eluz2n0
    adantr
    @1
    @58
    @0
    @59
    adantl
    expm1d
    eqcomd
    3brtr4d
    @38
    cr
    wcel
    @9
    @24
    @14
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @42
    @44
    wb
    c2
    c2
    2re
    2re
    remulcli
    @23
    @0
    @61
    @1
    @0
    @14
    @60
    @16
    @0
    cA
    @32
    nngt0d
    jca
    adantr
    @38
    @2
    cA
    lemuldiv
    mp3an2i
    mpbird
    eqbrtrrd
    letrd
    @9
    @2
    @23
    lep1d
    letrd
    @12
    @9
    @25
    @15
    cc0
    @4
    clt
    wbr
    #
    wa
    #
    @11
    @8
    wb
    2re
    @26
    @0
    @63
    @1
    @0
    @15
    @62
    @17
    @0
    cA
    cn
    wcel
    @19
    @62
    @32
    cA
    nnnn0
    cA
    nn0p1gt0
    3syl
    jca
    adantr
    c2
    @3
    @4
    lemuldiv
    mp3an2i
    mpbid
    3adant3
    @6
    @0
    @7
    @8
    wb
    @1
    cS
    @5
    c2
    cle
    breq2
    3ad2ant3
    mpbird
end
