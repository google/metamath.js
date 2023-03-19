include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "wo.mm"
include "df-sb.mm"
include "bj-sbsb.mm"
include "bitri.mm"

theorem bj-dfsb2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph <-> ( A. x ( x = y -> ph ) \/ ( x = y /\ ph ) ) )

  proof
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    wph
    wi
    #
    @0
    wph
    wa
    #
    vx
    wex
    wa
    @1
    vx
    wal
    @2
    wo
    wph
    vx
    vy
    df-sb
    wph
    vx
    vy
    bj-sbsb
    bitri
end
