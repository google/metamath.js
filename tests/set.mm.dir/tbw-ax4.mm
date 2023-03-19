include "falim.mm"

theorem tbw-ax4
  let wph: wff ph


  assert |- ( F. -> ph )

  proof
    wph
    falim
end
