include "wn.mm"
include "wo.mm"
include "exmid.mm"
include "a1i.mm"

theorem exmidd
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps \/ -. ps ) )

  proof
    wps
    wps
    wn
    wo
    wph
    wps
    exmid
    a1i
end
