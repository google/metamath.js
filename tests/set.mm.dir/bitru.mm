include "wtru.mm"
include "tru.mm"
include "2th.mm"

theorem bitru
  let wph: wff ph
  assume bitru.1: |- ph


  assert |- ( ph <-> T. )

  proof
    wph
    wtru
    bitru.1
    tru
    2th
end
