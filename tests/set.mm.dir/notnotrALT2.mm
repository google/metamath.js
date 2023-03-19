include "notnotr.mm"

theorem notnotrALT2
  let wph: wff ph


  assert |- ( -. -. ph -> ph )

  proof
    wph
    notnotr
end
