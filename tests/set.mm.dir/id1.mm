include "idALT.mm"

theorem id1
  let wph: wff ph


  assert |- ( ph -> ph )

  proof
    wph
    idALT
end
