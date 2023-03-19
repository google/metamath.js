include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cp1.mm"
include "cv.mm"
include "cbs.mm"
include "club.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq12d.mm"
include "df-p1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem p1val
  let cB: class B
  let cU: class U
  let c.1: class .1.
  let cK: class K
  let cV: class V
  let vk: setvar k
  assume p1val.b: |- B = ( Base ` K )
  assume p1val.u: |- U = ( lub ` K )
  assume p1val.t: |- .1. = ( 1. ` K )


  assert |- ( K e. V -> .1. = ( U ` B ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    #
    c.1
    cB
    cU
    cfv
    #
    wceq
    cK
    cV
    elex
    @0
    c.1
    cK
    cp1
    cfv
    @1
    p1val.t
    vk
    cK
    vk
    cv
    #
    cbs
    cfv
    #
    @2
    club
    cfv
    #
    cfv
    @1
    cvv
    cp1
    @2
    cK
    wceq
    #
    @3
    cB
    @4
    cU
    @5
    @4
    cK
    club
    cfv
    cU
    @2
    cK
    club
    fveq2
    p1val.u
    syl6eqr
    @5
    @3
    cK
    cbs
    cfv
    cB
    @2
    cK
    cbs
    fveq2
    p1val.b
    syl6eqr
    fveq12d
    vk
    df-p1
    cB
    cU
    fvex
    fvmpt
    syl5eq
    syl
end
