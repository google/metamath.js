include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfn.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "spcgf.mm"
include "con2d.mm"
include "df-ex.mm"
include "syl6ibr.mm"

theorem spcegf
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  param cV: class V
  assume spcgf.1: |- F/_ x A
  assume spcgf.2: |- F/ x ps
  assume spcgf.3: |- ( x = A -> ( ph <-> ps ) )


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
    spcgf.1
    wps
    vx
    spcgf.2
    nfn
    vx
    cv
    cA
    wceq
    wph
    wps
    spcgf.3
    notbid
    spcgf
    con2d
    wph
    vx
    df-ex
    syl6ibr
end
