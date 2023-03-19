include "id.mm"
include "imori.mm"

theorem pm2.1
  let wph: wff ph


  assert |- ( -. ph \/ ph )

  proof
    wph
    wph
    wph
    id
    imori
end
