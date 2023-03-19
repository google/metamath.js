include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "ccsh.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cshimadifsn.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "wi.mm"
include "cz.mm"
include "elfzoel2.mm"
include "elfzom1elp1fzo1.mm"
include "ex.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "wa.mm"
include "elfzo1elm1fzo0.mm"
include "adantl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "fveq2.mm"
include "cmo.mm"
include "adantr.mm"
include "1cnd.mm"
include "add32r.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "simpl1.mm"
include "peano2zd.mm"
include "wss.mm"
include "fzossrbm1.mm"
include "sseld.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "cshwidxmod.mm"
include "fzo0ss1.mm"
include "sylan.mm"
include "sseldi.mm"
include "3eqtr4rd.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "rexxfrd2.mm"
include "abbidv.mm"
include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "anim2i.mm"
include "3adant2.mm"
include "cshwfn.mm"
include "fnfun.mm"
include "syl5sseq.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "jca.mm"
include "mpdan.mm"
include "dfimafn.mm"
include "eqcoms.mm"
include "3eqtr4d.mm"

theorem cshimadifsn0
  let cS: class S
  let cF: class F
  let cJ: class J
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. Word S /\ N = ( # ` F ) /\ J e. ( 0 ..^ N ) ) -> ( F " ( ( 0 ..^ N ) \ { J } ) ) = ( ( F cyclShift ( J + 1 ) ) " ( 0 ..^ ( N - 1 ) ) ) )

  proof
    cF
    cS
    cword
    wcel
    #
    cN
    cF
    chash
    cfv
    #
    wceq
    #
    cJ
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cF
    @3
    cJ
    csn
    cdif
    cima
    cF
    cJ
    ccsh
    co
    #
    c1
    cN
    cfzo
    co
    #
    cima
    #
    cF
    cJ
    c1
    caddc
    co
    #
    ccsh
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cima
    #
    cS
    cF
    cJ
    cN
    cshimadifsn
    @5
    vx
    cv
    #
    @6
    cfv
    #
    vz
    cv
    #
    wceq
    #
    vx
    @7
    wrex
    #
    vz
    cab
    #
    vy
    cv
    #
    @10
    cfv
    #
    @16
    wceq
    #
    vy
    @12
    wrex
    #
    vz
    cab
    #
    @8
    @13
    @5
    @18
    @23
    vz
    @5
    @17
    @22
    vx
    vy
    @20
    c1
    caddc
    co
    #
    @7
    @12
    @5
    @20
    @12
    wcel
    #
    @25
    @7
    wcel
    #
    @4
    @0
    @26
    @27
    wi
    #
    @2
    @4
    cN
    cz
    wcel
    #
    @28
    cJ
    cc0
    cN
    elfzoel2
    #
    @29
    @26
    @27
    @20
    cN
    elfzom1elp1fzo1
    #
    ex
    syl
    3ad2ant3
    imp
    @5
    @14
    @7
    wcel
    #
    wa
    #
    @14
    @25
    wceq
    #
    @14
    @14
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vy
    @35
    @12
    @32
    @35
    @12
    wcel
    @5
    @14
    cN
    elfzo1elm1fzo0
    adantl
    @20
    @35
    wceq
    #
    @34
    @37
    wb
    @33
    @38
    @25
    @36
    @14
    @20
    @35
    c1
    caddc
    oveq1
    eqeq2d
    adantl
    @32
    @37
    @5
    @32
    @36
    @14
    @32
    @14
    cc
    wcel
    @36
    @14
    wceq
    @32
    @14
    @14
    c1
    cN
    elfzoelz
    zcnd
    @14
    npcan1
    syl
    eqcomd
    adantl
    rspcedvd
    @5
    @26
    @34
    w3a
    #
    @15
    @21
    @16
    @39
    @15
    @25
    @6
    cfv
    #
    @21
    @34
    @5
    @15
    @40
    wceq
    @26
    @14
    @25
    @6
    fveq2
    3ad2ant3
    @5
    @26
    @40
    @21
    wceq
    @34
    @5
    @26
    wa
    #
    @20
    @9
    caddc
    co
    #
    @1
    cmo
    co
    #
    cF
    cfv
    #
    @25
    cJ
    caddc
    co
    #
    @1
    cmo
    co
    #
    cF
    cfv
    #
    @21
    @40
    @41
    @43
    @46
    cF
    @41
    @42
    @45
    @1
    cmo
    @41
    @20
    cc
    wcel
    #
    cJ
    cc
    wcel
    #
    c1
    cc
    wcel
    @42
    @45
    wceq
    @26
    @48
    @5
    @26
    @20
    @20
    cc0
    @11
    elfzoelz
    zcnd
    adantl
    @5
    @49
    @26
    @4
    @0
    @49
    @2
    @4
    cJ
    cJ
    cc0
    cN
    elfzoelz
    #
    zcnd
    3ad2ant3
    adantr
    @41
    1cnd
    @20
    cJ
    c1
    add32r
    syl3anc
    oveq1d
    fveq2d
    @41
    @0
    @9
    cz
    wcel
    #
    @20
    cc0
    @1
    cfzo
    co
    #
    wcel
    #
    @21
    @44
    wceq
    @0
    @2
    @4
    @26
    simpl1
    #
    @5
    @51
    @26
    @4
    @0
    @51
    @2
    @4
    cJ
    @50
    peano2zd
    #
    3ad2ant3
    adantr
    @41
    @20
    @3
    wcel
    #
    @53
    @5
    @26
    @56
    @4
    @0
    @26
    @56
    wi
    @2
    @4
    @12
    @3
    @20
    @4
    @29
    @12
    @3
    wss
    #
    @30
    cN
    fzossrbm1
    syl
    #
    sseld
    3ad2ant3
    imp
    @5
    @56
    @53
    wb
    #
    @26
    @2
    @0
    @59
    @4
    @2
    @3
    @52
    @20
    cN
    @1
    cc0
    cfzo
    oveq2
    #
    eleq2d
    3ad2ant2
    adantr
    mpbid
    @20
    @9
    cS
    cF
    cshwidxmod
    syl3anc
    @41
    @0
    cJ
    cz
    wcel
    #
    @25
    @52
    wcel
    #
    @40
    @47
    wceq
    @54
    @5
    @61
    @26
    @4
    @0
    @61
    @2
    @50
    3ad2ant3
    adantr
    @41
    @25
    @3
    wcel
    #
    @62
    @41
    @7
    @3
    @25
    cN
    fzo0ss1
    #
    @5
    @29
    @26
    @27
    @4
    @0
    @29
    @2
    @30
    3ad2ant3
    @31
    sylan
    sseldi
    @5
    @63
    @62
    wb
    #
    @26
    @2
    @0
    @65
    @4
    @2
    @3
    @52
    @25
    @60
    eleq2d
    3ad2ant2
    adantr
    mpbid
    @25
    cJ
    cS
    cF
    cshwidxmod
    syl3anc
    3eqtr4rd
    3adant3
    eqtrd
    eqeq1d
    rexxfrd2
    abbidv
    @5
    @6
    wfun
    #
    @7
    @6
    cdm
    #
    wss
    #
    wa
    #
    @8
    @19
    wceq
    @5
    @6
    @52
    wfn
    #
    @69
    @5
    @0
    @61
    wa
    #
    @70
    @0
    @4
    @71
    @2
    @4
    @61
    @0
    @50
    anim2i
    3adant2
    cJ
    cS
    cF
    cshwfn
    syl
    @5
    @70
    wa
    #
    @66
    @68
    @70
    @66
    @5
    @52
    @6
    fnfun
    adantl
    @72
    @7
    @52
    @67
    @5
    @7
    @52
    wss
    @70
    @5
    @3
    @7
    @52
    @64
    @2
    @0
    @3
    @52
    wceq
    @4
    @60
    3ad2ant2
    syl5sseq
    adantr
    @70
    @67
    @52
    wceq
    @5
    @52
    @6
    fndm
    adantl
    sseqtr4d
    jca
    mpdan
    vx
    vz
    @7
    @6
    dfimafn
    syl
    @5
    @10
    wfun
    #
    @12
    @10
    cdm
    #
    wss
    #
    wa
    #
    @13
    @24
    wceq
    @5
    @10
    @52
    wfn
    #
    @76
    @5
    @0
    @51
    wa
    #
    @77
    @0
    @4
    @78
    @2
    @4
    @51
    @0
    @55
    anim2i
    3adant2
    @9
    cS
    cF
    cshwfn
    syl
    @5
    @77
    wa
    #
    @73
    @75
    @77
    @73
    @5
    @52
    @10
    fnfun
    adantl
    @79
    @12
    @52
    @74
    @5
    @12
    @52
    wss
    @77
    @5
    @12
    @3
    @52
    @4
    @0
    @57
    @2
    @58
    3ad2ant3
    @2
    @0
    @52
    @3
    wceq
    #
    @4
    @80
    @1
    cN
    @1
    cN
    cc0
    cfzo
    oveq2
    eqcoms
    3ad2ant2
    sseqtr4d
    adantr
    @77
    @74
    @52
    wceq
    @5
    @52
    @10
    fndm
    adantl
    sseqtr4d
    jca
    mpdan
    vy
    vz
    @12
    @10
    dfimafn
    syl
    3eqtr4d
    eqtrd
end
