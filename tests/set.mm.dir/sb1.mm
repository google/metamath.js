include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "df-sb.mm"
include "simprbi.mm"

theorem sb1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) )

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
    @0
    wph
    wa
    vx
    wex
    wph
    vx
    vy
    df-sb
    simprbi
end
