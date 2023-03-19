include "wo.mm"
include "orc.mm"
include "id.mm"
include "jaoi.mm"

theorem pm2.4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) )

  proof
    wph
    wph
    wps
    wo
    #
    @0
    wph
    wps
    orc
    @0
    id
    jaoi
end
