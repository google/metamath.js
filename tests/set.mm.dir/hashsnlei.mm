include "csn.mm"
include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "snfi.mm"
include "hashsnle1.mm"
include "pm3.2i.mm"

theorem hashsnlei
  let cA: class A


  assert |- ( { A } e. Fin /\ ( # ` { A } ) <_ 1 )

  proof
    cA
    csn
    #
    cfn
    wcel
    @0
    chash
    cfv
    c1
    cle
    wbr
    cA
    snfi
    cA
    hashsnle1
    pm3.2i
end
