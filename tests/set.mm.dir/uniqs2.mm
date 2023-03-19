include "cqs.mm"
include "cuni.mm"
include "crn.mm"
include "cdm.mm"
include "cima.mm"
include "wcel.mm"
include "wceq.mm"
include "uniqs.mm"
include "syl.mm"
include "wer.mm"
include "erdm.mm"
include "imaeq2d.mm"
include "eqtr4d.mm"
include "imadmrn.mm"
include "syl6eq.mm"
include "errn.mm"
include "eqtrd.mm"

theorem uniqs2
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume qsss.1: |- ( ph -> R Er A )
  assume qsss.2: |- ( ph -> R e. V )


  assert |- ( ph -> U. ( A /. R ) = A )

  proof
    wph
    cA
    cR
    cqs
    cuni
    #
    cR
    crn
    #
    cA
    wph
    @0
    cR
    cR
    cdm
    #
    cima
    #
    @1
    wph
    @0
    cR
    cA
    cima
    #
    @3
    wph
    cR
    cV
    wcel
    @0
    @4
    wceq
    qsss.2
    cA
    cR
    cV
    uniqs
    syl
    wph
    @2
    cA
    cR
    wph
    cA
    cR
    wer
    #
    @2
    cA
    wceq
    qsss.1
    cA
    cR
    erdm
    syl
    imaeq2d
    eqtr4d
    cR
    imadmrn
    syl6eq
    wph
    @5
    @1
    cA
    wceq
    qsss.1
    cA
    cR
    errn
    syl
    eqtrd
end
