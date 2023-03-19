include "wsb.mm"
include "sbid.mm"
include "imbi2i.mm"

theorem sbidd-misc
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( ph -> [ x / x ] ps ) <-> ( ph -> ps ) )

  proof
    wps
    vx
    vx
    wsb
    wps
    wph
    wps
    vx
    sbid
    imbi2i
end
