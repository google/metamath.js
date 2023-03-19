include "notnot.mm"

theorem axfrege41
  let wph: wff ph


  assert |- ( ph -> -. -. ph )

  proof
    wph
    notnot
end
