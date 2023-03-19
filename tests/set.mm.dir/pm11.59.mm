include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "wa.mm"
include "nfv.mm"
include "nfal.mm"
include "sp.mm"
include "spsbim.mm"
include "anim12d.mm"
include "axc4i.mm"
include "alrimi.mm"

theorem pm11.59
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint ps y
  assert |- ( A. x ( ph -> ps ) -> A. y A. x ( ( ph /\ [ y / x ] ph ) -> ( ps /\ [ y / x ] ps ) ) )

  proof
    wph
    wps
    wi
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
    wa
    wps
    wps
    vx
    vy
    wsb
    #
    wa
    wi
    #
    vx
    wal
    vy
    @0
    vy
    vx
    @0
    vy
    nfv
    nfal
    @0
    @4
    vx
    @1
    wph
    wps
    @2
    @3
    @0
    vx
    sp
    wph
    wps
    vx
    vy
    spsbim
    anim12d
    axc4i
    alrimi
end
