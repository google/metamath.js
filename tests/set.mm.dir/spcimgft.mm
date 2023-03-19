include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "elex.mm"
include "wex.mm"
include "issetf.mm"
include "exim.mm"
include "syl5bi.mm"
include "19.36.mm"
include "syl6ib.mm"
include "syl5.mm"

theorem spcimgft
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume spcimgft.1: |- F/ x ps
  assume spcimgft.2: |- F/_ x A


  assert |- ( A. x ( x = A -> ( ph -> ps ) ) -> ( A e. B -> ( A. x ph -> ps ) ) )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    #
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wi
    #
    wi
    vx
    wal
    #
    wph
    vx
    wal
    wps
    wi
    #
    cA
    cB
    elex
    @3
    @0
    @2
    vx
    wex
    #
    @4
    @0
    @1
    vx
    wex
    @3
    @5
    vx
    cA
    spcimgft.2
    issetf
    @1
    @2
    vx
    exim
    syl5bi
    wph
    wps
    vx
    spcimgft.1
    19.36
    syl6ib
    syl5
end
