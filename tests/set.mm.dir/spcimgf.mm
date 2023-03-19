include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wcel.mm"
include "wal.mm"
include "spcimgft.mm"
include "mpg.mm"

theorem spcimgf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume spcimgf.1: |- F/_ x A
  assume spcimgf.2: |- F/ x ps
  assume spcimgf.3: |- ( x = A -> ( ph -> ps ) )


  assert |- ( A e. V -> ( A. x ph -> ps ) )

  proof
    vx
    cv
    cA
    wceq
    wph
    wps
    wi
    wi
    cA
    cV
    wcel
    wph
    vx
    wal
    wps
    wi
    wi
    vx
    wph
    wps
    vx
    cA
    cV
    spcimgf.2
    spcimgf.1
    spcimgft
    spcimgf.3
    mpg
end
