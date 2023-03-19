include "wsb.mm"
include "sbid.mm"
include "sylib.mm"

theorem sbidd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k
  assume sbidd.1: |- ( ph -> [ x / x ] ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    vx
    vx
    wsb
    wps
    sbidd.1
    wps
    vx
    sbid
    sylib
end
