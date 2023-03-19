include "cgbo.mm"
include "wcel.mm"
include "cgbow.mm"
include "codd.mm"
include "gbogbow.mm"
include "gbowodd.mm"
include "syl.mm"

theorem gboodd
  let cZ: class Z
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOdd -> Z e. Odd )

  proof
    cZ
    cgbo
    wcel
    cZ
    cgbow
    wcel
    cZ
    codd
    wcel
    cZ
    gbogbow
    cZ
    gbowodd
    syl
end
