include "cep.mm"
include "corvc.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "cr.mm"
include "crab.mm"
include "cima.mm"
include "cbrsiga.mm"
include "orrvcval4.mm"
include "wcel.mm"
include "cin.mm"
include "wb.mm"
include "epelg.mm"
include "syl.mm"
include "rabbidv.mm"
include "wceq.mm"
include "dfin5.mm"
include "a1i.mm"
include "wss.mm"
include "cuni.mm"
include "elssuni.mm"
include "unibrsiga.mm"
include "syl6sseq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "3eqtr2d.mm"
include "imaeq2d.mm"
include "eqtrd.mm"

theorem orvcelval
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume dstrvprob.1: |- ( ph -> P e. Prob )
  assume dstrvprob.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orvcelel.1: |- ( ph -> A e. BrSiga )


  assert |- ( ph -> ( X oRVC _E A ) = ( `' X " A ) )

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
    vx
    cv
    #
    cA
    cep
    wbr
    #
    vx
    cr
    crab
    #
    cima
    @0
    cA
    cima
    wph
    vx
    cA
    cP
    cep
    cbrsiga
    cX
    dstrvprob.1
    dstrvprob.2
    orvcelel.1
    orrvcval4
    wph
    @3
    cA
    @0
    wph
    @3
    @1
    cA
    wcel
    #
    vx
    cr
    crab
    #
    cr
    cA
    cin
    #
    cA
    wph
    @2
    @4
    vx
    cr
    wph
    cA
    cbrsiga
    wcel
    #
    @2
    @4
    wb
    orvcelel.1
    @1
    cA
    cbrsiga
    epelg
    syl
    rabbidv
    @6
    @5
    wceq
    wph
    vx
    cr
    cA
    dfin5
    a1i
    wph
    cA
    cr
    wss
    #
    @6
    cA
    wceq
    wph
    @7
    @8
    orvcelel.1
    @7
    cA
    cbrsiga
    cuni
    cr
    cA
    cbrsiga
    elssuni
    unibrsiga
    syl6sseq
    syl
    cA
    cr
    sseqin2
    sylib
    3eqtr2d
    imaeq2d
    eqtrd
end
