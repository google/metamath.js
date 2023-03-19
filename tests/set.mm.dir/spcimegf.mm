include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfn.mm"
include "cv.mm"
include "wceq.mm"
include "con3d.mm"
include "spcimgf.mm"
include "con2d.mm"
include "df-ex.mm"
include "syl6ibr.mm"

theorem spcimegf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume spcimgf.1: |- F/_ x A
  assume spcimgf.2: |- F/ x ps
  assume spcimegf.3: |- ( x = A -> ( ps -> ph ) )


  assert |- ( A e. V -> ( ps -> E. x ph ) )

  proof
    cA
    cV
    wcel
    #
    wps
    wph
    wn
    #
    vx
    wal
    #
    wn
    wph
    vx
    wex
    @0
    @2
    wps
    @1
    wps
    wn
    vx
    cA
    cV
    spcimgf.1
    wps
    vx
    spcimgf.2
    nfn
    vx
    cv
    cA
    wceq
    wps
    wph
    spcimegf.3
    con3d
    spcimgf
    con2d
    wph
    vx
    df-ex
    syl6ibr
end
