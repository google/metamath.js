include "cc.mm"
include "csin.mm"
include "sinf.mm"
include "ffvelrni.mm"

theorem sincl
  let cA: class A


  assert |- ( A e. CC -> ( sin ` A ) e. CC )

  proof
    cc
    cc
    cA
    csin
    sinf
    ffvelrni
end
