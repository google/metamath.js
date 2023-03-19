include "id.mm"
include "e0a.mm"

theorem idiVD
  let wph: wff ph
  assume idiVD.1: |- ph


  assert |- ph

  proof
    wph
    wph
    idiVD.1
    wph
    id
    e0a
end
