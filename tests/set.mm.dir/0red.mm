include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "0re.mm"
include "a1i.mm"

theorem 0red
  let wph: wff ph


  assert |- ( ph -> 0 e. RR )

  proof
    cc0
    cr
    wcel
    wph
    0re
    a1i
end
