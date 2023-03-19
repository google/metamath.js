include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "a1i.mm"

theorem 1zzd
  let wph: wff ph


  assert |- ( ph -> 1 e. ZZ )

  proof
    c1
    cz
    wcel
    wph
    1z
    a1i
end
