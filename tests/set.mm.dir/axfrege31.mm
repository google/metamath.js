include "notnotr.mm"

theorem axfrege31
  let wph: wff ph


  assert |- ( -. -. ph -> ph )

  proof
    wph
    notnotr
end
