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
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "ccsh.mm"
include "c1.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "wfn.mm"
include "wrdfn.mm"
include "fnfun.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "wrddm.mm"
include "difssd.mm"
include "oveq2.mm"
include "difeq1d.mm"
include "adantl.mm"
include "simpl.mm"
include "3sstr4d.mm"
include "a1d.mm"
include "ex.mm"
include "3imp.mm"
include "jca.mm"
include "dfimafn.mm"
include "caddc.mm"
include "cmo.mm"
include "modsumfzodifsn.mm"
include "3ad2antl3.mm"
include "wb.mm"
include "eqcoms.mm"
include "eleq1d.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "mpbird.mm"
include "modfzo0difsn.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "fveq2.mm"
include "3ad2ant3.mm"
include "cz.mm"
include "simpl1.mm"
include "elfzoelz.mm"
include "eleq2d.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "syl6bi.mm"
include "imp.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "rexxfrd2.mm"
include "abbidv.mm"
include "anim2i.mm"
include "3adant2.mm"
include "cshwfn.mm"
include "syl6eqss.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "mpdan.mm"

theorem cshimadifsn
  let cS: class S
  let cF: class F
  let cJ: class J
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. Word S /\ N = ( # ` F ) /\ J e. ( 0 ..^ N ) ) -> ( F " ( ( 0 ..^ N ) \ { J } ) ) = ( ( F cyclShift J ) " ( 1 ..^ N ) ) )

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
    #
    cdif
    #
    cima
    #
    vx
    cv
    #
    cF
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
    @5
    cF
    wfun
    #
    @7
    cF
    cdm
    #
    wss
    #
    wa
    @8
    @14
    wceq
    @5
    @18
    @20
    @0
    @2
    @18
    @4
    @0
    cF
    cc0
    @1
    cfzo
    co
    #
    wfn
    @18
    cS
    cF
    wrdfn
    @21
    cF
    fnfun
    syl
    3ad2ant1
    @0
    @2
    @4
    @20
    @0
    @19
    @21
    wceq
    #
    @2
    @4
    @20
    wi
    #
    wi
    cS
    cF
    wrddm
    @22
    @2
    @23
    @22
    @2
    wa
    #
    @20
    @4
    @24
    @21
    @6
    cdif
    #
    @21
    @7
    @19
    @24
    @21
    @6
    difssd
    @2
    @7
    @25
    wceq
    @22
    @2
    @3
    @21
    @6
    cN
    @1
    cc0
    cfzo
    oveq2
    difeq1d
    adantl
    @22
    @2
    simpl
    3sstr4d
    a1d
    ex
    syl
    3imp
    jca
    vx
    vz
    @7
    cF
    dfimafn
    syl
    @5
    @14
    vy
    cv
    #
    @15
    cfv
    #
    @11
    wceq
    #
    vy
    @16
    wrex
    #
    vz
    cab
    #
    @17
    @5
    @13
    @29
    vz
    @5
    @12
    @28
    vx
    vy
    @26
    cJ
    caddc
    co
    #
    @1
    cmo
    co
    #
    @7
    @16
    @5
    @26
    @16
    wcel
    #
    wa
    #
    @32
    @7
    wcel
    #
    @31
    cN
    cmo
    co
    #
    @7
    wcel
    #
    @4
    @0
    @33
    @37
    @2
    cJ
    @26
    cN
    modsumfzodifsn
    3ad2antl3
    @5
    @35
    @37
    wb
    #
    @33
    @2
    @0
    @38
    @4
    @2
    @32
    @36
    @7
    @32
    @36
    wceq
    @1
    cN
    @1
    cN
    @31
    cmo
    oveq2
    eqcoms
    eleq1d
    3ad2ant2
    adantr
    mpbird
    @5
    @9
    @7
    wcel
    #
    wa
    @9
    @32
    wceq
    #
    vy
    @16
    wrex
    #
    @9
    @36
    wceq
    #
    vy
    @16
    wrex
    #
    @4
    @0
    @39
    @43
    @2
    vy
    cJ
    @9
    cN
    modfzo0difsn
    3ad2antl3
    @5
    @41
    @43
    wb
    #
    @39
    @2
    @0
    @44
    @4
    @2
    @40
    @42
    vy
    @16
    @2
    @32
    @36
    @9
    @2
    @36
    @32
    cN
    @1
    @31
    cmo
    oveq2
    eqcomd
    eqeq2d
    rexbidv
    3ad2ant2
    adantr
    mpbird
    @5
    @33
    @40
    w3a
    #
    @10
    @27
    @11
    @45
    @10
    @32
    cF
    cfv
    #
    @27
    @40
    @5
    @10
    @46
    wceq
    @33
    @9
    @32
    cF
    fveq2
    3ad2ant3
    @5
    @33
    @46
    @27
    wceq
    #
    @40
    @34
    @0
    cJ
    cz
    wcel
    #
    @26
    @21
    wcel
    #
    @47
    @0
    @2
    @4
    @33
    simpl1
    @5
    @48
    @33
    @4
    @0
    @48
    @2
    cJ
    cc0
    cN
    elfzoelz
    #
    3ad2ant3
    adantr
    @5
    @33
    @49
    @2
    @0
    @33
    @49
    wi
    @4
    @2
    @33
    @26
    c1
    @1
    cfzo
    co
    #
    wcel
    @49
    @2
    @16
    @51
    @26
    cN
    @1
    c1
    cfzo
    oveq2
    #
    eleq2d
    @51
    @21
    @26
    @1
    fzo0ss1
    #
    sseli
    syl6bi
    3ad2ant2
    imp
    @0
    @48
    @49
    w3a
    @27
    @46
    @26
    cJ
    cS
    cF
    cshwidxmod
    eqcomd
    syl3anc
    3adant3
    eqtrd
    eqeq1d
    rexxfrd2
    abbidv
    @5
    @17
    @30
    @5
    @15
    wfun
    #
    @16
    @15
    cdm
    #
    wss
    #
    wa
    #
    @17
    @30
    wceq
    @5
    @15
    @21
    wfn
    #
    @57
    @5
    @0
    @48
    wa
    #
    @58
    @0
    @4
    @59
    @2
    @4
    @48
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
    @58
    wa
    #
    @54
    @56
    @58
    @54
    @5
    @21
    @15
    fnfun
    adantl
    @60
    @16
    @21
    @55
    @5
    @16
    @21
    wss
    #
    @58
    @2
    @0
    @61
    @4
    @2
    @16
    @51
    @21
    @52
    @53
    syl6eqss
    3ad2ant2
    adantr
    @58
    @55
    @21
    wceq
    @5
    @21
    @15
    fndm
    adantl
    sseqtr4d
    jca
    mpdan
    vy
    vz
    @16
    @15
    dfimafn
    syl
    eqcomd
    eqtrd
    eqtrd
end
