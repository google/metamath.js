include "ax-1.mm"

theorem tbw-ax2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ph ) )

  proof
    wph
    wps
    ax-1
end
