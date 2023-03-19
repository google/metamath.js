include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "a1i.mm"

theorem 1cnd
  let wph: wff ph


  assert |- ( ph -> 1 e. CC )

  proof
    c1
    cc
    wcel
    wph
    ax-1cn
    a1i
end
