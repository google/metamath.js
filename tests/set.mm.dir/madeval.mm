include "con0.mm"
include "wcel.mm"
include "cmade.mm"
include "cfv.mm"
include "cres.mm"
include "cvv.mm"
include "cscut.mm"
include "cv.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "cxp.mm"
include "cima.mm"
include "cmpt.mm"
include "df-made.mm"
include "tfr2.mm"
include "wceq.mm"
include "wfun.mm"
include "wfn.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "resfunexg.mm"
include "mpan.mm"
include "csslt.mm"
include "csur.mm"
include "wf.mm"
include "scutf.mm"
include "ffun.mm"
include "funimaexg.mm"
include "uniexg.mm"
include "pwexg.mm"
include "3syl.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "sylancr.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "unieqd.mm"
include "pweqd.mm"
include "sqxpeqd.mm"
include "imaeq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "eqtrd.mm"

theorem madeval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( _M ` A ) = ( |s " ( ~P U. ( _M " A ) X. ~P U. ( _M " A ) ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cmade
    cfv
    cmade
    cA
    cres
    #
    vx
    cvv
    cscut
    vx
    cv
    #
    crn
    #
    cuni
    #
    cpw
    #
    @5
    cxp
    #
    cima
    #
    cmpt
    #
    cfv
    #
    cscut
    cmade
    cA
    cima
    #
    cuni
    #
    cpw
    #
    @12
    cxp
    #
    cima
    #
    cA
    cmade
    @8
    vx
    df-made
    #
    tfr2
    @0
    @1
    cvv
    wcel
    #
    @14
    cvv
    wcel
    #
    @9
    @14
    wceq
    cmade
    wfun
    #
    @0
    @16
    cmade
    con0
    wfn
    @18
    cmade
    @8
    @15
    tfr1
    con0
    cmade
    fnfun
    ax-mp
    #
    cmade
    cA
    con0
    resfunexg
    mpan
    @0
    cscut
    wfun
    #
    @13
    cvv
    wcel
    #
    @17
    csslt
    csur
    cscut
    wf
    @20
    scutf
    csslt
    csur
    cscut
    ffun
    ax-mp
    @0
    @12
    cvv
    wcel
    #
    @22
    @21
    @0
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @22
    @18
    @0
    @23
    @19
    cmade
    cA
    con0
    funimaexg
    mpan
    @10
    cvv
    uniexg
    @11
    cvv
    pwexg
    3syl
    #
    @24
    @12
    @12
    cvv
    cvv
    xpexg
    syl2anc
    cscut
    @13
    cvv
    funimaexg
    sylancr
    vx
    @1
    @7
    @14
    cvv
    cvv
    @8
    @2
    @1
    wceq
    #
    @6
    @13
    cscut
    @25
    @5
    @12
    @25
    @4
    @11
    @25
    @3
    @10
    @25
    @3
    @1
    crn
    @10
    @2
    @1
    rneq
    cmade
    cA
    df-ima
    syl6eqr
    unieqd
    pweqd
    sqxpeqd
    imaeq2d
    @8
    eqid
    fvmptg
    syl2anc
    eqtrd
end
