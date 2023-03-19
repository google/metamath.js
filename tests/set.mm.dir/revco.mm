include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "creverse.mm"
include "cfv.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "c1.mm"
include "cmin.mm"
include "wfn.mm"
include "wceq.mm"
include "wrdfn.mm"
include "ad2antrr.mm"
include "cfz.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "syl.mm"
include "adantr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "fznn0sub2.mm"
include "eleqtrrd.mm"
include "fvco2.mm"
include "syl2anc.mm"
include "lenco.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "revfv.mm"
include "adantlr.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "revlen.mm"
include "3eqtr4rd.mm"
include "simpr.mm"
include "revcl.mm"
include "wrdf.mm"
include "fcompt.mm"
include "cvv.mm"
include "wfun.mm"
include "ffun.mm"
include "adantl.mm"
include "simpl.mm"
include "cofunexg.mm"
include "revval.mm"

theorem revco
  let cA: class A
  let cB: class B
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T


  assert |- ( ( W e. Word A /\ F : A --> B ) -> ( F o. ( reverse ` W ) ) = ( reverse ` ( F o. W ) ) )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    cA
    cB
    cF
    wf
    #
    wa
    #
    vx
    cc0
    cW
    creverse
    cfv
    #
    chash
    cfv
    #
    cfzo
    co
    #
    vx
    cv
    #
    @4
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    vx
    cc0
    cF
    cW
    ccom
    #
    chash
    cfv
    #
    cfzo
    co
    #
    @12
    c1
    cmin
    co
    #
    @7
    cmin
    co
    #
    @11
    cfv
    #
    cmpt
    #
    cF
    @4
    ccom
    #
    @11
    creverse
    cfv
    #
    @3
    vx
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    @16
    cmpt
    vx
    @21
    @9
    cmpt
    @17
    @10
    @3
    vx
    @21
    @16
    @9
    @3
    @7
    @21
    wcel
    #
    wa
    #
    @20
    c1
    cmin
    co
    #
    @7
    cmin
    co
    #
    @11
    cfv
    #
    @25
    cW
    cfv
    #
    cF
    cfv
    #
    @16
    @9
    @23
    cW
    @21
    wfn
    #
    @25
    @21
    wcel
    @26
    @28
    wceq
    @1
    @29
    @2
    @22
    cA
    cW
    wrdfn
    ad2antrr
    @23
    @25
    cc0
    @24
    cfz
    co
    #
    @21
    @23
    @7
    @30
    wcel
    #
    @25
    @30
    wcel
    @3
    @22
    @31
    @3
    @21
    @30
    @7
    @1
    @21
    @30
    wceq
    #
    @2
    @1
    @20
    cz
    wcel
    @32
    @1
    @20
    cA
    cW
    lencl
    nn0zd
    cc0
    @20
    fzoval
    syl
    adantr
    #
    eleq2d
    biimpa
    @7
    @24
    fznn0sub2
    syl
    @3
    @32
    @22
    @33
    adantr
    eleqtrrd
    @21
    cF
    cW
    @25
    fvco2
    syl2anc
    @23
    @15
    @25
    @11
    @3
    @15
    @25
    wceq
    @22
    @3
    @14
    @24
    @7
    cmin
    @3
    @12
    @20
    c1
    cmin
    cA
    cB
    cF
    cW
    lenco
    #
    oveq1d
    oveq1d
    adantr
    fveq2d
    @23
    @8
    @27
    cF
    @1
    @22
    @8
    @27
    wceq
    @2
    cA
    cW
    @7
    revfv
    adantlr
    fveq2d
    3eqtr4d
    mpteq2dva
    @3
    vx
    @13
    @21
    @16
    @3
    @12
    @20
    cc0
    cfzo
    @34
    oveq2d
    mpteq1d
    @3
    vx
    @6
    @21
    @9
    @3
    @5
    @20
    cc0
    cfzo
    @1
    @5
    @20
    wceq
    @2
    cA
    cW
    revlen
    adantr
    oveq2d
    mpteq1d
    3eqtr4rd
    @3
    @2
    @6
    cA
    @4
    wf
    #
    @18
    @10
    wceq
    @1
    @2
    simpr
    @1
    @35
    @2
    @1
    @4
    @0
    wcel
    @35
    cA
    cW
    revcl
    cA
    @4
    wrdf
    syl
    adantr
    vx
    cF
    @4
    @6
    cA
    cB
    fcompt
    syl2anc
    @3
    @11
    cvv
    wcel
    #
    @19
    @17
    wceq
    @3
    cF
    wfun
    #
    @1
    @36
    @2
    @37
    @1
    cA
    cB
    cF
    ffun
    adantl
    @1
    @2
    simpl
    cF
    cW
    @0
    cofunexg
    syl2anc
    vx
    cvv
    @11
    revval
    syl
    3eqtr4d
end
