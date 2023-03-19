include "wal.mm"
include "wb.mm"
include "wtru.mm"
include "nftru.mm"
include "weq.mm"
include "wn.mm"
include "wnf.mm"
include "wi.mm"
include "a1i.mm"
include "wl-cbvalnaed.mm"
include "trud.mm"

theorem wl-cbvalnae
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume wl-cbvalnae.1: |- ( -. A. x x = y -> F/ y ph )
  assume wl-cbvalnae.2: |- ( -. A. x x = y -> F/ x ps )
  assume wl-cbvalnae.3: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x ph <-> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    wal
    wb
    wtru
    wph
    wps
    vx
    vy
    vx
    nftru
    vy
    nftru
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    wph
    vy
    wnf
    wi
    wtru
    wl-cbvalnae.1
    a1i
    @1
    wps
    vx
    wnf
    wi
    wtru
    wl-cbvalnae.2
    a1i
    @0
    wph
    wps
    wb
    wi
    wtru
    wl-cbvalnae.3
    a1i
    wl-cbvalnaed
    trud
end
