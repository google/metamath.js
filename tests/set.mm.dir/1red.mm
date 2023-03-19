include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "1re.mm"
include "a1i.mm"

theorem 1red
  let wph: wff ph


  assert |- ( ph -> 1 e. RR )

  proof
    c1
    cr
    wcel
    wph
    1re
    a1i
end
