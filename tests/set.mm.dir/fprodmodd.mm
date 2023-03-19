include "cv.mm"
include "cprod.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "prodeq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "c1.mm"
include "prod0.mm"
include "a1i.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "csb.mm"
include "cmul.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "cfn.mm"
include "wi.mm"
include "ssfi.mm"
include "ex.mm"
include "syl11.mm"
include "adantr.mm"
include "impcom.mm"
include "simpr.mm"
include "adantl.mm"
include "wn.mm"
include "eldifn.mm"
include "cz.mm"
include "simpll.mm"
include "ssel.mm"
include "imp.mm"
include "syl2anc.mm"
include "zcnd.mm"
include "csbeq1a.mm"
include "wral.mm"
include "eldifi.mm"
include "ralrimiva.mm"
include "rspcsbela.mm"
include "syl2anr.mm"
include "fprodsplitsn.mm"
include "fprodzcl.mm"
include "crp.mm"
include "nnrpd.mm"
include "wsbc.mm"
include "rspsbca.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbceqg.mm"
include "mp1i.mm"
include "mpbid.mm"
include "csbov1g.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "modmul12d.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "findcard2d.mm"

theorem fprodmodd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cM: class M
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  assume fprodmodd.a: |- ( ph -> A e. Fin )
  assume fprodmodd.b: |- ( ( ph /\ k e. A ) -> B e. ZZ )
  assume fprodmodd.c: |- ( ( ph /\ k e. A ) -> C e. ZZ )
  assume fprodmodd.m: |- ( ph -> M e. NN )
  assume fprodmodd.p: |- ( ( ph /\ k e. A ) -> ( B mod M ) = ( C mod M ) )

  disjoint A k
  disjoint M k
  disjoint k ph
  disjoint A i
  disjoint A x
  disjoint A y
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B i
  disjoint B x
  disjoint B y
  disjoint C i
  disjoint C x
  disjoint C y
  disjoint M i
  disjoint M x
  disjoint M y
  disjoint i ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( prod_ k e. A B mod M ) = ( prod_ k e. A C mod M ) )

  proof
    wph
    vx
    cv
    #
    cB
    vk
    cprod
    #
    cM
    cmo
    co
    #
    @0
    cC
    vk
    cprod
    #
    cM
    cmo
    co
    #
    wceq
    c0
    cB
    vk
    cprod
    #
    cM
    cmo
    co
    #
    c0
    cC
    vk
    cprod
    #
    cM
    cmo
    co
    #
    wceq
    vy
    cv
    #
    cB
    vk
    cprod
    #
    cM
    cmo
    co
    #
    @9
    cC
    vk
    cprod
    #
    cM
    cmo
    co
    #
    wceq
    #
    @9
    vi
    cv
    #
    csn
    cun
    #
    cB
    vk
    cprod
    #
    cM
    cmo
    co
    #
    @16
    cC
    vk
    cprod
    #
    cM
    cmo
    co
    #
    wceq
    #
    cA
    cB
    vk
    cprod
    #
    cM
    cmo
    co
    #
    cA
    cC
    vk
    cprod
    #
    cM
    cmo
    co
    #
    wceq
    vx
    vy
    vi
    cA
    @0
    c0
    wceq
    #
    @2
    @6
    @4
    @8
    @26
    @1
    @5
    cM
    cmo
    @0
    c0
    cB
    vk
    prodeq1
    oveq1d
    @26
    @3
    @7
    cM
    cmo
    @0
    c0
    cC
    vk
    prodeq1
    oveq1d
    eqeq12d
    @0
    @9
    wceq
    #
    @2
    @11
    @4
    @13
    @27
    @1
    @10
    cM
    cmo
    @0
    @9
    cB
    vk
    prodeq1
    oveq1d
    @27
    @3
    @12
    cM
    cmo
    @0
    @9
    cC
    vk
    prodeq1
    oveq1d
    eqeq12d
    @0
    @16
    wceq
    #
    @2
    @18
    @4
    @20
    @28
    @1
    @17
    cM
    cmo
    @0
    @16
    cB
    vk
    prodeq1
    oveq1d
    @28
    @3
    @19
    cM
    cmo
    @0
    @16
    cC
    vk
    prodeq1
    oveq1d
    eqeq12d
    @0
    cA
    wceq
    #
    @2
    @23
    @4
    @25
    @29
    @1
    @22
    cM
    cmo
    @0
    cA
    cB
    vk
    prodeq1
    oveq1d
    @29
    @3
    @24
    cM
    cmo
    @0
    cA
    cC
    vk
    prodeq1
    oveq1d
    eqeq12d
    wph
    @6
    c1
    cM
    cmo
    co
    @8
    wph
    @5
    c1
    cM
    cmo
    @5
    c1
    wceq
    wph
    cB
    vk
    prod0
    a1i
    oveq1d
    c1
    @7
    cM
    cmo
    @7
    c1
    cC
    vk
    prod0
    eqcomi
    oveq1i
    syl6eq
    wph
    @9
    cA
    wss
    #
    @15
    cA
    @9
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    @14
    @21
    @34
    @14
    wa
    #
    @18
    @10
    vk
    @15
    cB
    csb
    #
    cmul
    co
    #
    cM
    cmo
    co
    #
    @12
    vk
    @15
    cC
    csb
    #
    cmul
    co
    #
    cM
    cmo
    co
    #
    @20
    @34
    @18
    @38
    wceq
    @14
    @34
    @17
    @37
    cM
    cmo
    @34
    @9
    @15
    cB
    @36
    vk
    @31
    @34
    vk
    nfv
    #
    vk
    @15
    cB
    nfcsb1v
    @33
    wph
    @9
    cfn
    wcel
    #
    @30
    wph
    @43
    wi
    @32
    cA
    cfn
    wcel
    #
    @30
    @43
    wph
    @44
    @30
    @43
    cA
    @9
    ssfi
    ex
    fprodmodd.a
    syl11
    adantr
    impcom
    #
    @33
    @32
    wph
    @30
    @32
    simpr
    adantl
    #
    @33
    @15
    @9
    wcel
    wn
    #
    wph
    @32
    @47
    @30
    @15
    cA
    @9
    eldifn
    adantl
    adantl
    #
    @34
    vk
    cv
    #
    @9
    wcel
    #
    wa
    #
    cB
    @51
    wph
    @49
    cA
    wcel
    #
    cB
    cz
    wcel
    #
    wph
    @33
    @50
    simpll
    #
    @34
    @50
    @52
    @33
    @50
    @52
    wi
    #
    wph
    @30
    @55
    @32
    @9
    cA
    @49
    ssel
    adantr
    adantl
    imp
    #
    fprodmodd.b
    syl2anc
    #
    zcnd
    vk
    @15
    cB
    csbeq1a
    @34
    @36
    @33
    @15
    cA
    wcel
    #
    @53
    vk
    cA
    wral
    @36
    cz
    wcel
    #
    wph
    @32
    @58
    @30
    @15
    cA
    @9
    eldifi
    adantl
    #
    wph
    @53
    vk
    cA
    fprodmodd.b
    ralrimiva
    vk
    @15
    cA
    cB
    cz
    rspcsbela
    syl2anr
    #
    zcnd
    fprodsplitsn
    oveq1d
    adantr
    @35
    @10
    @12
    @36
    @39
    cM
    @34
    @10
    cz
    wcel
    @14
    @34
    @9
    cB
    vk
    @45
    @57
    fprodzcl
    adantr
    @34
    @12
    cz
    wcel
    @14
    @34
    @9
    cC
    vk
    @45
    @51
    wph
    @52
    cC
    cz
    wcel
    #
    @54
    @56
    fprodmodd.c
    syl2anc
    #
    fprodzcl
    adantr
    @34
    @59
    @14
    @61
    adantr
    @34
    @39
    cz
    wcel
    #
    @14
    @33
    @58
    @62
    vk
    cA
    wral
    @64
    wph
    @60
    wph
    @62
    vk
    cA
    fprodmodd.c
    ralrimiva
    vk
    @15
    cA
    cC
    cz
    rspcsbela
    syl2anr
    #
    adantr
    @34
    cM
    crp
    wcel
    #
    @14
    wph
    @66
    @33
    wph
    cM
    fprodmodd.m
    nnrpd
    adantr
    adantr
    @34
    @14
    simpr
    @34
    @36
    cM
    cmo
    co
    #
    @39
    cM
    cmo
    co
    #
    wceq
    @14
    @34
    vk
    @15
    cB
    cM
    cmo
    co
    #
    csb
    #
    vk
    @15
    cC
    cM
    cmo
    co
    #
    csb
    #
    @67
    @68
    @34
    @69
    @71
    wceq
    #
    vk
    @15
    wsbc
    #
    @70
    @72
    wceq
    #
    @33
    @58
    @73
    vk
    cA
    wral
    @74
    wph
    @60
    wph
    @73
    vk
    cA
    fprodmodd.p
    ralrimiva
    @73
    vk
    @15
    cA
    rspsbca
    syl2anr
    @15
    cvv
    wcel
    #
    @74
    @75
    wb
    @34
    vi
    vex
    #
    vk
    @15
    @69
    @71
    cvv
    sbceqg
    mp1i
    mpbid
    @76
    @70
    @67
    wceq
    @77
    vk
    @15
    cB
    cM
    cmo
    cvv
    csbov1g
    ax-mp
    @76
    @72
    @68
    wceq
    @77
    vk
    @15
    cC
    cM
    cmo
    cvv
    csbov1g
    ax-mp
    3eqtr3g
    adantr
    modmul12d
    @34
    @41
    @20
    wceq
    @14
    @34
    @20
    @41
    @34
    @19
    @40
    cM
    cmo
    @34
    @9
    @15
    cC
    @39
    vk
    @31
    @42
    vk
    @15
    cC
    nfcsb1v
    @45
    @46
    @48
    @51
    cC
    @63
    zcnd
    vk
    @15
    cC
    csbeq1a
    @34
    @39
    @65
    zcnd
    fprodsplitsn
    oveq1d
    eqcomd
    adantr
    3eqtrd
    ex
    fprodmodd.a
    findcard2d
end
