include "cvv.mm"
include "wcel.mm"
include "cfullfn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cfunpart.mm"
include "cdm.mm"
include "cdif.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "df-fullfun.mm"
include "fveq1i.mm"
include "cin.mm"
include "disjdif.mm"
include "wfn.mm"
include "wa.mm"
include "wfun.mm"
include "funpartfun.mm"
include "funfn.mm"
include "mpbi.mm"
include "wf.mm"
include "0ex.mm"
include "fconst.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fvun1.mm"
include "mp3an12.mm"
include "mpan.mm"
include "wn.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "fvun2.mm"
include "fvconst2.mm"
include "eqtrd.mm"
include "sylbir.mm"
include "ndmfv.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "funpartfv.mm"
include "3eqtri.mm"
include "vtoclg.mm"
include "fvprc.mm"

theorem fullfunfv
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( FullFun F ` A ) = ( F ` A )

  proof
    cA
    cvv
    wcel
    #
    cA
    cF
    cfullfn
    #
    cfv
    #
    cA
    cF
    cfv
    #
    wceq
    #
    vx
    cv
    #
    @1
    cfv
    #
    @5
    cF
    cfv
    #
    wceq
    @4
    vx
    cA
    cvv
    @5
    cA
    wceq
    @6
    @2
    @7
    @3
    @5
    cA
    @1
    fveq2
    @5
    cA
    cF
    fveq2
    eqeq12d
    @6
    @5
    cF
    cfunpart
    #
    cvv
    @8
    cdm
    #
    cdif
    #
    c0
    csn
    #
    cxp
    #
    cun
    #
    cfv
    #
    @5
    @8
    cfv
    #
    @7
    @5
    @1
    @13
    cF
    df-fullfun
    fveq1i
    @5
    @9
    wcel
    #
    @14
    @15
    wceq
    #
    @9
    @10
    cin
    c0
    wceq
    #
    @16
    @17
    @9
    cvv
    disjdif
    #
    @8
    @9
    wfn
    #
    @12
    @10
    wfn
    #
    @18
    @16
    wa
    @17
    @8
    wfun
    @20
    cF
    funpartfun
    @8
    funfn
    mpbi
    #
    @10
    @11
    @12
    wf
    @21
    @10
    c0
    0ex
    fconst
    @10
    @11
    @12
    ffn
    ax-mp
    #
    @9
    @10
    @8
    @12
    @5
    fvun1
    mp3an12
    mpan
    @16
    wn
    #
    @14
    c0
    @15
    @24
    @5
    @10
    wcel
    #
    @14
    c0
    wceq
    @25
    @5
    cvv
    wcel
    @24
    vx
    vex
    @5
    cvv
    @9
    eldif
    mpbiran
    @25
    @14
    @5
    @12
    cfv
    #
    c0
    @18
    @25
    @14
    @26
    wceq
    #
    @19
    @20
    @21
    @18
    @25
    wa
    @27
    @22
    @23
    @9
    @10
    @8
    @12
    @5
    fvun2
    mp3an12
    mpan
    @10
    c0
    @5
    0ex
    fvconst2
    eqtrd
    sylbir
    @5
    @8
    ndmfv
    eqtr4d
    pm2.61i
    @5
    cF
    funpartfv
    3eqtri
    vtoclg
    @0
    wn
    @2
    c0
    @3
    cA
    @1
    fvprc
    cA
    cF
    fvprc
    eqtr4d
    pm2.61i
end
