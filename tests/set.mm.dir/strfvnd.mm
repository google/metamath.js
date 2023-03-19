include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "fveq1.mm"
include "cslot.mm"
include "cmpt.mm"
include "df-slot.mm"
include "eqtri.mm"
include "fvex.mm"
include "fvmpt.mm"
include "3syl.mm"

theorem strfvnd
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cN: class N
  let cV: class V
  let vx: setvar x
  assume strfvnd.c: |- E = Slot N
  assume strfvnd.f: |- ( ph -> S e. V )


  assert |- ( ph -> ( E ` S ) = ( S ` N ) )

  proof
    wph
    cS
    cV
    wcel
    cS
    cvv
    wcel
    cS
    cE
    cfv
    cN
    cS
    cfv
    #
    wceq
    strfvnd.f
    cS
    cV
    elex
    vx
    cS
    cN
    vx
    cv
    #
    cfv
    #
    @0
    cvv
    cE
    cN
    @1
    cS
    fveq1
    cE
    cN
    cslot
    vx
    cvv
    @2
    cmpt
    strfvnd.c
    vx
    cN
    df-slot
    eqtri
    cN
    cS
    fvex
    fvmpt
    3syl
end
