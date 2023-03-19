include "cqs.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "vex.mm"
include "elqs.mm"
include "wss.mm"
include "ecss.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "selpw.mm"
include "syl6ibr.mm"
include "rexlimdvw.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem qsss
  let wph: wff ph
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume qsss.1: |- ( ph -> R Er A )


  assert |- ( ph -> ( A /. R ) C_ ~P A )

  proof
    wph
    vx
    cA
    cR
    cqs
    #
    cA
    cpw
    #
    vx
    cv
    #
    @0
    wcel
    @2
    vy
    cv
    #
    cR
    cec
    #
    wceq
    #
    vy
    cA
    wrex
    wph
    @2
    @1
    wcel
    #
    vy
    cA
    @2
    cR
    vx
    vex
    elqs
    wph
    @5
    @6
    vy
    cA
    wph
    @5
    @2
    cA
    wss
    #
    @6
    wph
    @7
    @5
    @4
    cA
    wss
    wph
    @3
    cR
    cA
    qsss.1
    ecss
    @2
    @4
    cA
    sseq1
    syl5ibrcom
    vx
    cA
    selpw
    syl6ibr
    rexlimdvw
    syl5bi
    ssrdv
end
