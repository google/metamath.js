include "pm2.01.mm"

theorem axin1
  let wph: wff ph


  assert |- ( ( ph -> -. ph ) -> -. ph )

  proof
    wph
    pm2.01
end
