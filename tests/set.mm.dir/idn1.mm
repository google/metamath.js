include "id.mm"
include "dfvd1ir.mm"

theorem idn1
  let wph: wff ph


  assert |- (. ph ->. ph ).

  proof
    wph
    wph
    wph
    id
    dfvd1ir
end
