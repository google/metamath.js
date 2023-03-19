include "wnf.mm"
include "wal.mm"
include "wsb.mm"
include "nfa1.mm"
include "nfnf1.mm"
include "nfal.mm"
include "sp.mm"
include "wl-nfs1t.mm"
include "sps.mm"
include "weq.mm"
include "wb.mm"
include "wi.mm"
include "sbequ12.mm"
include "a1i.mm"
include "cbv2.mm"

theorem wl-sb8t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> ( A. x ph <-> A. y [ y / x ] ph ) )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    @0
    vx
    nfa1
    @0
    vy
    vx
    wph
    vy
    nfnf1
    nfal
    @0
    vx
    sp
    @0
    @2
    vx
    wnf
    vx
    wph
    vx
    vy
    wl-nfs1t
    sps
    vx
    vy
    weq
    wph
    @2
    wb
    wi
    @1
    wph
    vx
    vy
    sbequ12
    a1i
    cbv2
end
