include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "stdpc4.mm"
include "sbi1.mm"
include "syl.mm"

theorem spsbim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    @0
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    wps
    vx
    vy
    wsb
    wi
    @0
    vx
    vy
    stdpc4
    wph
    wps
    vx
    vy
    sbi1
    syl
end
