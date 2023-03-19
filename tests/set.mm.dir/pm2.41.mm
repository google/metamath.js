include "wo.mm"
include "olc.mm"
include "id.mm"
include "jaoi.mm"

theorem pm2.41
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) )

  proof
    wps
    wph
    wps
    wo
    #
    @0
    wps
    wph
    olc
    @0
    id
    jaoi
end
