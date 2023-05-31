include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "biimp.mm"
include "imim2i.mm"
include "alimi.mm"
include "spcimgft.mm"
include "syl.mm"

theorem spcgft
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume spcimgft.1: |- F/ x ps
  assume spcimgft.2: |- F/_ x A


  assert |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B -> ( A. x ph -> ps ) ) )

  proof
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    @0
    wph
    wps
    wi
    #
    wi
    #
    vx
    wal
    cA
    cB
    wcel
    wph
    vx
    wal
    wps
    wi
    wi
    @2
    @4
    vx
    @1
    @3
    @0
    wph
    wps
    biimp
    imim2i
    alimi
    wph
    wps
    vx
    cA
    cB
    spcimgft.1
    spcimgft.2
    spcimgft
    syl
end
