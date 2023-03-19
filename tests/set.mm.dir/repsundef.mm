include "cn0.mm"
include "wnel.mm"
include "creps.mm"
include "cdm.mm"
include "cvv.mm"
include "cxp.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "cmpt.mm"
include "df-reps.mm"
include "ovex.mm"
include "mptex.mm"
include "dmmpt2.mm"
include "df-nel.mm"
include "biimpi.mm"
include "intnand.mm"
include "ndmovg.mm"
include "sylancr.mm"

theorem repsundef
  let cS: class S
  let cN: class N
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x


  assert |- ( N e/ NN0 -> ( S repeatS N ) = (/) )

  proof
    cN
    cn0
    wnel
    #
    creps
    cdm
    cvv
    cn0
    cxp
    wceq
    cS
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    wn
    cS
    cN
    creps
    co
    c0
    wceq
    vs
    vn
    cvv
    cn0
    vx
    cc0
    vn
    cv
    #
    cfzo
    co
    #
    vs
    cv
    #
    cmpt
    creps
    vx
    vn
    vs
    df-reps
    vx
    @4
    @5
    cc0
    @3
    cfzo
    ovex
    mptex
    dmmpt2
    @0
    @2
    @1
    @0
    @2
    wn
    cN
    cn0
    df-nel
    biimpi
    intnand
    cS
    cN
    cvv
    cn0
    creps
    ndmovg
    sylancr
end
