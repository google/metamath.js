include "cgbo.mm"
include "wcel.mm"
include "cgbow.mm"
include "cn.mm"
include "gbogbow.mm"
include "gbowpos.mm"
include "syl.mm"

theorem gbopos
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOdd -> Z e. NN )

  proof
    cZ
    cgbo
    wcel
    cZ
    cgbow
    wcel
    cZ
    cn
    wcel
    cZ
    gbogbow
    cZ
    gbowpos
    syl
end
