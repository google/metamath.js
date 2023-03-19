include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "ccom.mm"
include "w3a.mm"
include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cdm.mm"
include "cin.mm"
include "cima.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "simpr1.mm"
include "fvimacnvi.mm"
include "sylan.mm"
include "wfn.mm"
include "wceq.mm"
include "funfn.mm"
include "sylib.mm"
include "dffn5.mm"
include "reseq1d.mm"
include "wss.mm"
include "cnvimass.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "offval3.mm"
include "adantr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fmptco.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "fndm.mm"
include "syl.mm"
include "eqimss.mm"
include "cores2.mm"
include "3syl.mm"
include "funcnvres2.mm"
include "coeq2d.mm"
include "eqtr3d.mm"
include "simpr2.mm"
include "simpr3.mm"
include "syl2anc.mm"
include "inpreima.mm"
include "dmco.mm"
include "ineq12i.mm"
include "syl6reqr.mm"
include "simplr1.mm"
include "inss2.mm"
include "dmcoss.mm"
include "sstri.mm"
include "a1i.mm"
include "sselda.mm"
include "fvco.mm"
include "inss1.mm"
include "mpteq12dva.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem ofco2
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( F e. _V /\ G e. _V ) /\ ( Fun H /\ ( F o. H ) e. _V /\ ( G o. H ) e. _V ) ) -> ( ( F oF R G ) o. H ) = ( ( F o. H ) oF R ( G o. H ) ) )

  proof
    cF
    cvv
    wcel
    cG
    cvv
    wcel
    wa
    #
    cH
    wfun
    #
    cF
    cH
    ccom
    #
    cvv
    wcel
    #
    cG
    cH
    ccom
    #
    cvv
    wcel
    #
    w3a
    #
    wa
    #
    cF
    cG
    cR
    cof
    #
    co
    #
    cH
    cH
    ccnv
    #
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    cima
    #
    cres
    #
    ccom
    #
    vx
    @14
    vx
    cv
    #
    cH
    cfv
    #
    cF
    cfv
    #
    @18
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    @9
    cH
    ccom
    #
    @2
    @4
    @8
    co
    #
    @7
    vx
    vy
    @14
    @13
    @18
    vy
    cv
    #
    cF
    cfv
    #
    @25
    cG
    cfv
    #
    cR
    co
    #
    @21
    @15
    @9
    @7
    @1
    @17
    @14
    wcel
    @18
    @13
    wcel
    @0
    @1
    @3
    @5
    simpr1
    #
    @17
    @13
    cH
    fvimacnvi
    sylan
    @7
    @15
    vx
    cH
    cdm
    #
    @18
    cmpt
    #
    @14
    cres
    #
    vx
    @14
    @18
    cmpt
    #
    @7
    cH
    @31
    @14
    @7
    cH
    @30
    wfn
    #
    cH
    @31
    wceq
    @7
    @1
    @34
    @29
    cH
    funfn
    sylib
    vx
    @30
    cH
    dffn5
    sylib
    reseq1d
    @14
    @30
    wss
    @32
    @33
    wceq
    cH
    @13
    cnvimass
    vx
    @30
    @14
    @18
    resmpt
    ax-mp
    syl6eq
    @0
    @9
    vy
    @13
    @28
    cmpt
    wceq
    @6
    vy
    cR
    cF
    cG
    cvv
    cvv
    offval3
    adantr
    @25
    @18
    wceq
    @26
    @19
    @27
    @20
    cR
    @25
    @18
    cF
    fveq2
    @25
    @18
    cG
    fveq2
    oveq12d
    fmptco
    @7
    @9
    @10
    @13
    cres
    ccnv
    #
    ccom
    #
    @23
    @16
    @7
    @9
    cdm
    #
    @13
    wceq
    #
    @37
    @13
    wss
    @36
    @23
    wceq
    @7
    @9
    @13
    wfn
    #
    @38
    @7
    @39
    vx
    @13
    @17
    cF
    cfv
    #
    @17
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    @13
    wfn
    #
    @42
    cvv
    wcel
    #
    vx
    @13
    wral
    @44
    @7
    @45
    vx
    @13
    @40
    @41
    cR
    ovex
    rgenw
    vx
    @13
    @42
    @43
    cvv
    @43
    eqid
    fnmpt
    mp1i
    @7
    @13
    @9
    @43
    @0
    @9
    @43
    wceq
    @6
    vx
    cR
    cF
    cG
    cvv
    cvv
    offval3
    adantr
    fneq1d
    mpbird
    @13
    @9
    fndm
    syl
    @37
    @13
    eqimss
    @9
    cH
    @13
    cores2
    3syl
    @7
    @35
    @15
    @9
    @7
    @1
    @35
    @15
    wceq
    @29
    @13
    cH
    funcnvres2
    syl
    coeq2d
    eqtr3d
    @7
    @24
    vx
    @2
    cdm
    #
    @4
    cdm
    #
    cin
    #
    @17
    @2
    cfv
    #
    @17
    @4
    cfv
    #
    cR
    co
    #
    cmpt
    #
    @22
    @7
    @3
    @5
    @24
    @52
    wceq
    @0
    @1
    @3
    @5
    simpr2
    @0
    @1
    @3
    @5
    simpr3
    vx
    cR
    @2
    @4
    cvv
    cvv
    offval3
    syl2anc
    @7
    vx
    @48
    @51
    @14
    @21
    @7
    @14
    @10
    @11
    cima
    #
    @10
    @12
    cima
    #
    cin
    #
    @48
    @7
    @1
    @14
    @55
    wceq
    @29
    @11
    @12
    cH
    inpreima
    syl
    @46
    @53
    @47
    @54
    cF
    cH
    dmco
    cG
    cH
    dmco
    ineq12i
    syl6reqr
    @7
    @17
    @48
    wcel
    #
    wa
    #
    @49
    @19
    @50
    @20
    cR
    @57
    @1
    @17
    @30
    wcel
    #
    @49
    @19
    wceq
    @1
    @3
    @5
    @0
    @56
    simplr1
    #
    @7
    @48
    @30
    @17
    @48
    @30
    wss
    #
    @7
    @48
    @47
    @30
    @46
    @47
    inss2
    cG
    cH
    dmcoss
    sstri
    a1i
    sselda
    @17
    cF
    cH
    fvco
    syl2anc
    @57
    @1
    @58
    @50
    @20
    wceq
    @59
    @7
    @48
    @30
    @17
    @60
    @7
    @48
    @46
    @30
    @46
    @47
    inss1
    cF
    cH
    dmcoss
    sstri
    a1i
    sselda
    @17
    cG
    cH
    fvco
    syl2anc
    oveq12d
    mpteq12dva
    eqtrd
    3eqtr4d
end
