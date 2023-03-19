include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wcel.mm"
include "wal.mm"
include "spcgft.mm"
include "mpg.mm"

theorem spcgf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume spcgf.1: |- F/_ x A
  assume spcgf.2: |- F/ x ps
  assume spcgf.3: |- ( x = A -> ( ph <-> ps ) )


  assert |- ( A e. V -> ( A. x ph -> ps ) )

  proof
    vx
    cv
    cA
    wceq
    wph
    wps
    wb
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
    spcgf.2
    spcgf.1
    spcgft
    spcgf.3
    mpg
end
