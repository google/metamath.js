include "wi.mm"
include "wsb.mm"
include "sbi1.mm"
include "sbi2.mm"
include "impbii.mm"

theorem sbim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) )

  proof
    wph
    wps
    wi
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
    wph
    wps
    vx
    vy
    sbi1
    wph
    wps
    vx
    vy
    sbi2
    impbii
end
