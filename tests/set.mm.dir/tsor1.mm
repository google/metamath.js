include "wo.mm"
include "exmidd.mm"

theorem tsor1
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( ph \/ ps ) \/ -. ( ph \/ ps ) ) )

  proof
    wth
    wph
    wps
    wo
    exmidd
end
