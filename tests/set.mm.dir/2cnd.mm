include "c2.mm"
include "cc.mm"
include "wcel.mm"
include "2cn.mm"
include "a1i.mm"

theorem 2cnd
  let wph: wff ph


  assert |- ( ph -> 2 e. CC )

  proof
    c2
    cc
    wcel
    wph
    2cn
    a1i
end
