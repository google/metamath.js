include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "cful.mm"
include "co.mm"
include "cfunc.mm"
include "wss.mm"
include "cv.mm"
include "wceq.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "oveq2.mm"
include "wbr.mm"
include "crn.mm"
include "cfv.mm"
include "chom.mm"
include "cbs.mm"
include "wral.mm"
include "copab.mm"
include "cvv.mm"
include "ovex.mm"
include "simpl.mm"
include "ssopab2i.mm"
include "opabss.mm"
include "sstri.mm"
include "ssexi.mm"
include "df-full.mm"
include "ovmpt4g.mm"
include "mp3an3.mm"
include "syl6eqss.mm"
include "vtocl2ga.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem fullfunc
  let cC: class C
  let cD: class D
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( C Full D ) C_ ( C Func D )

  proof
    cC
    ccat
    wcel
    cD
    ccat
    wcel
    wa
    #
    cC
    cD
    cful
    co
    #
    cC
    cD
    cfunc
    co
    #
    wss
    #
    vc
    cv
    #
    vd
    cv
    #
    cful
    co
    #
    @4
    @5
    cfunc
    co
    #
    wss
    cC
    @5
    cful
    co
    #
    cC
    @5
    cfunc
    co
    #
    wss
    @3
    vc
    vd
    cC
    cD
    ccat
    ccat
    @4
    cC
    wceq
    @6
    @8
    @7
    @9
    @4
    cC
    @5
    cful
    oveq1
    @4
    cC
    @5
    cfunc
    oveq1
    sseq12d
    @5
    cD
    wceq
    @8
    @1
    @9
    @2
    @5
    cD
    cC
    cful
    oveq2
    @5
    cD
    cC
    cfunc
    oveq2
    sseq12d
    @4
    ccat
    wcel
    #
    @5
    ccat
    wcel
    #
    wa
    @6
    vf
    cv
    #
    vg
    cv
    #
    @7
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    @13
    co
    crn
    @15
    @12
    cfv
    @16
    @12
    cfv
    @5
    chom
    cfv
    co
    wceq
    vy
    @4
    cbs
    cfv
    #
    wral
    vx
    @17
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    @7
    @10
    @11
    @20
    cvv
    wcel
    @6
    @20
    wceq
    @20
    @7
    @4
    @5
    cfunc
    ovex
    @20
    @14
    vf
    vg
    copab
    @7
    @19
    @14
    vf
    vg
    @14
    @18
    simpl
    ssopab2i
    vf
    vg
    @7
    opabss
    sstri
    #
    ssexi
    vc
    vd
    ccat
    ccat
    @20
    cful
    cvv
    vx
    vy
    vf
    vg
    vc
    vd
    df-full
    #
    ovmpt4g
    mp3an3
    @21
    syl6eqss
    vtocl2ga
    @0
    wn
    @1
    c0
    @2
    vc
    vd
    @20
    cful
    cC
    cD
    ccat
    ccat
    @22
    mpt2ndm0
    @2
    0ss
    syl6eqss
    pm2.61i
end
