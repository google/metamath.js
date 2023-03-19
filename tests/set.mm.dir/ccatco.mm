include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cconcat.mm"
include "wceq.mm"
include "lenco.mm"
include "3adant2.mm"
include "3adant1.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "wa.mm"
include "adantr.mm"
include "eleq2d.mm"
include "ifbid.mm"
include "wfn.mm"
include "wrdf.mm"
include "3ad2ant1.mm"
include "ffn.mm"
include "syl.mm"
include "fvco2.mm"
include "sylan.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "cz.mm"
include "wo.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzospliti.mm"
include "ancoms.mm"
include "orcanai.mm"
include "fzosubel3.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "iffalse.mm"
include "3eqtr4d.mm"
include "ifeqda.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "eqtr2d.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "ifclda.mm"
include "ccatfval.mm"
include "3adant3.mm"
include "simp3.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fvif.mm"
include "syl6eq.mm"
include "fmptco.mm"
include "cvv.mm"
include "wfun.mm"
include "ffun.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "cofunexg.mm"
include "simp2.mm"

theorem ccatco
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cW: class W


  assert |- ( ( S e. Word A /\ T e. Word A /\ F : A --> B ) -> ( F o. ( S ++ T ) ) = ( ( F o. S ) ++ ( F o. T ) ) )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cA
    cB
    cF
    wf
    #
    w3a
    #
    vx
    cc0
    cS
    chash
    cfv
    #
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @5
    cfzo
    co
    #
    wcel
    #
    @9
    cS
    cfv
    #
    cF
    cfv
    #
    @9
    @5
    cmin
    co
    #
    cT
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    vx
    cc0
    cF
    cS
    ccom
    #
    chash
    cfv
    #
    cF
    cT
    ccom
    #
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    @9
    cc0
    @20
    cfzo
    co
    #
    wcel
    #
    @9
    @19
    cfv
    #
    @9
    @20
    cmin
    co
    #
    @21
    cfv
    #
    cif
    #
    cmpt
    #
    cF
    cS
    cT
    cconcat
    co
    #
    ccom
    @19
    @21
    cconcat
    co
    #
    @4
    @31
    vx
    @8
    @30
    cmpt
    @18
    @4
    vx
    @24
    @8
    @30
    @4
    @23
    @7
    cc0
    cfzo
    @4
    @20
    @5
    @22
    @6
    caddc
    @1
    @3
    @20
    @5
    wceq
    @2
    cA
    cB
    cF
    cS
    lenco
    3adant2
    #
    @2
    @3
    @22
    @6
    wceq
    @1
    cA
    cB
    cF
    cT
    lenco
    3adant1
    oveq12d
    oveq2d
    mpteq1d
    @4
    vx
    @8
    @30
    @17
    @4
    @9
    @8
    wcel
    #
    wa
    #
    @30
    @11
    @27
    @29
    cif
    @17
    @36
    @26
    @11
    @27
    @29
    @36
    @25
    @10
    @9
    @4
    @25
    @10
    wceq
    @35
    @4
    @20
    @5
    cc0
    cfzo
    @34
    oveq2d
    adantr
    eleq2d
    ifbid
    @36
    @11
    @27
    @29
    @17
    @36
    @11
    wa
    @27
    @13
    @17
    @36
    cS
    @10
    wfn
    #
    @11
    @27
    @13
    wceq
    @36
    @10
    cA
    cS
    wf
    #
    @37
    @4
    @38
    @35
    @1
    @2
    @38
    @3
    cA
    cS
    wrdf
    3ad2ant1
    adantr
    #
    @10
    cA
    cS
    ffn
    syl
    @10
    cF
    cS
    @9
    fvco2
    sylan
    @11
    @17
    @13
    wceq
    @36
    @11
    @13
    @16
    iftrue
    adantl
    eqtr4d
    @36
    @11
    wn
    #
    wa
    #
    @14
    @21
    cfv
    #
    @16
    @29
    @17
    @41
    cT
    cc0
    @6
    cfzo
    co
    #
    wfn
    #
    @14
    @43
    wcel
    #
    @42
    @16
    wceq
    @41
    @43
    cA
    cT
    wf
    #
    @44
    @4
    @46
    @35
    @40
    @2
    @1
    @46
    @3
    cA
    cT
    wrdf
    3ad2ant2
    ad2antrr
    #
    @43
    cA
    cT
    ffn
    syl
    @41
    @9
    @5
    @7
    cfzo
    co
    wcel
    #
    @6
    cz
    wcel
    #
    @45
    @36
    @11
    @48
    @4
    @5
    cz
    wcel
    #
    @35
    @11
    @48
    wo
    #
    @1
    @2
    @50
    @3
    @1
    @5
    cA
    cS
    lencl
    nn0zd
    3ad2ant1
    @35
    @50
    @51
    @9
    cc0
    @7
    @5
    fzospliti
    ancoms
    sylan
    orcanai
    @4
    @49
    @35
    @40
    @2
    @1
    @49
    @3
    @2
    @6
    cA
    cT
    lencl
    nn0zd
    3ad2ant2
    ad2antrr
    @9
    @5
    @6
    fzosubel3
    syl2anc
    #
    @43
    cF
    cT
    @14
    fvco2
    syl2anc
    @4
    @29
    @42
    wceq
    @35
    @40
    @4
    @28
    @14
    @21
    @4
    @20
    @5
    @9
    cmin
    @34
    oveq2d
    fveq2d
    ad2antrr
    @40
    @17
    @16
    wceq
    @36
    @11
    @13
    @16
    iffalse
    adantl
    3eqtr4d
    ifeqda
    eqtrd
    mpteq2dva
    eqtr2d
    @4
    vx
    vy
    @8
    cA
    @11
    @12
    @15
    cif
    #
    vy
    cv
    #
    cF
    cfv
    #
    @17
    @32
    cF
    @36
    @11
    @12
    @15
    cA
    @36
    @10
    cA
    @9
    cS
    @39
    ffvelrnda
    @41
    @43
    cA
    @14
    cT
    @47
    @52
    ffvelrnd
    ifclda
    @1
    @2
    @32
    vx
    @8
    @53
    cmpt
    wceq
    @3
    vx
    cS
    cT
    @0
    @0
    ccatfval
    3adant3
    @4
    vy
    cA
    cB
    cF
    @1
    @2
    @3
    simp3
    feqmptd
    @54
    @53
    wceq
    @55
    @53
    cF
    cfv
    @17
    @54
    @53
    cF
    fveq2
    @11
    @12
    @15
    cF
    fvif
    syl6eq
    fmptco
    @4
    @19
    cvv
    wcel
    #
    @21
    cvv
    wcel
    #
    @33
    @31
    wceq
    @4
    cF
    wfun
    #
    @1
    @56
    @3
    @1
    @58
    @2
    cA
    cB
    cF
    ffun
    3ad2ant3
    #
    @1
    @2
    @3
    simp1
    cF
    cS
    @0
    cofunexg
    syl2anc
    @4
    @58
    @2
    @57
    @59
    @1
    @2
    @3
    simp2
    cF
    cT
    @0
    cofunexg
    syl2anc
    vx
    @19
    @21
    cvv
    cvv
    ccatfval
    syl2anc
    3eqtr4d
end
