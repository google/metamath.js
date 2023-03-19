include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "xpss.mm"
include "sseli.mm"
include "copsex2gb.mm"
include "baibr.mm"
include "syl.mm"

theorem copsex2ga
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let cW: class W
  assume copsex2ga.1: |- ( A = <. x , y >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  assert |- ( A e. ( V X. W ) -> ( ph <-> E. x E. y ( A = <. x , y >. /\ ps ) ) )

  proof
    cA
    cV
    cW
    cxp
    #
    wcel
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    wph
    cA
    vx
    cv
    vy
    cv
    cop
    wceq
    wps
    wa
    vy
    wex
    vx
    wex
    #
    wb
    @0
    @1
    cA
    cV
    cW
    xpss
    sseli
    @3
    @2
    wph
    wph
    wps
    vx
    vy
    cA
    copsex2ga.1
    copsex2gb
    baibr
    syl
end
