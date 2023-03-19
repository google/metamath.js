include "id.mm"
include "jaoi.mm"

theorem pm1.2
  let wph: wff ph


  assert |- ( ( ph \/ ph ) -> ph )

  proof
    wph
    wph
    wph
    wph
    id
    #
    @0
    jaoi
end
