include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "wtru.mm"
include "nftru.mm"
include "wnf.mm"
include "a1i.mm"
include "wl-equsald.mm"
include "trud.mm"

theorem wl-equsal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume wl-equsal.1: |- F/ x ps
  assume wl-equsal.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x ( x = y -> ph ) <-> ps )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    wps
    wb
    wtru
    wph
    wps
    vx
    vy
    vx
    nftru
    wps
    vx
    wnf
    wtru
    wl-equsal.1
    a1i
    @0
    wph
    wps
    wb
    wi
    wtru
    wl-equsal.2
    a1i
    wl-equsald
    trud
end
