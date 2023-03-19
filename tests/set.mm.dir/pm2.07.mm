include "olc.mm"

theorem pm2.07
  let wph: wff ph


  assert |- ( ph -> ( ph \/ ph ) )

  proof
    wph
    wph
    olc
end
