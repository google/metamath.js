include "wnf.mm"
include "weq.mm"
include "wsb.mm"
include "wi.mm"
include "wal.mm"
include "nfnf1.mm"
include "id.mm"
include "wb.mm"
include "sbequ12r.mm"
include "a1i.mm"
include "wl-equsald.mm"
include "bicomd.mm"

theorem wl-sb6rft
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/ x ph -> ( ph <-> A. x ( x = y -> [ x / y ] ph ) ) )

  proof
    wph
    vx
    wnf
    #
    vx
    vy
    weq
    #
    wph
    vy
    vx
    wsb
    #
    wi
    vx
    wal
    wph
    @0
    @2
    wph
    vx
    vy
    wph
    vx
    nfnf1
    @0
    id
    @1
    @2
    wph
    wb
    wi
    @0
    wph
    vx
    vy
    sbequ12r
    a1i
    wl-equsald
    bicomd
end
