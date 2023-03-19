include "wsb.mm"
include "wi.mm"
include "wn.mm"
include "sbn.mm"
include "pm2.21.mm"
include "sbimi.mm"
include "sylbir.mm"
include "ax-1.mm"
include "ja.mm"

theorem sbi2
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y


  assert |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) )

  proof
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    wph
    wps
    wi
    #
    vx
    vy
    wsb
    #
    @0
    wn
    wph
    wn
    #
    vx
    vy
    wsb
    @2
    wph
    vx
    vy
    sbn
    @3
    @1
    vx
    vy
    wph
    wps
    pm2.21
    sbimi
    sylbir
    wps
    @1
    vx
    vy
    wps
    wph
    ax-1
    sbimi
    ja
end
