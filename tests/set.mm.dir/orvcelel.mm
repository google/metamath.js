include "cep.mm"
include "corvc.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "orvcelval.mm"
include "cv.mm"
include "wcel.mm"
include "cbrsiga.mm"
include "wral.mm"
include "rrvfinvima.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "rspcdv.mm"
include "mpd.mm"
include "eqeltrd.mm"

theorem orvcelel
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume dstrvprob.1: |- ( ph -> P e. Prob )
  assume dstrvprob.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orvcelel.1: |- ( ph -> A e. BrSiga )


  assert |- ( ph -> ( X oRVC _E A ) e. dom P )

  proof
    wph
    cX
    cA
    cep
    corvc
    co
    cX
    ccnv
    #
    cA
    cima
    #
    cP
    cdm
    #
    wph
    cA
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    orvcelel.1
    orvcelval
    wph
    @0
    va
    cv
    #
    cima
    #
    @2
    wcel
    #
    va
    cbrsiga
    wral
    @1
    @2
    wcel
    #
    wph
    va
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    rrvfinvima
    wph
    @5
    @6
    va
    cA
    cbrsiga
    orvcelel.1
    wph
    @3
    cA
    wceq
    #
    wa
    #
    @4
    @1
    @2
    @8
    @3
    cA
    @0
    wph
    @7
    simpr
    imaeq2d
    eleq1d
    rspcdv
    mpd
    eqeltrd
end
