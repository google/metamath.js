include "cnpi.mm"
include "wcel.mm"
include "com.mm"
include "word.mm"
include "pinn.mm"
include "nnord.mm"
include "syl.mm"

theorem piord
  let cA: class A


  assert |- ( A e. N. -> Ord A )

  proof
    cA
    cnpi
    wcel
    cA
    com
    wcel
    cA
    word
    cA
    pinn
    cA
    nnord
    syl
end
