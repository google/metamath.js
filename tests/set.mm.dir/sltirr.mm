include "csur.mm"
include "cslt.mm"
include "wor.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"

theorem sltirr
  let cA: class A


  assert |- ( A e. No -> -. A <s A )

  proof
    csur
    cslt
    wor
    cA
    csur
    wcel
    cA
    cA
    cslt
    wbr
    wn
    sltso
    csur
    cA
    cslt
    sonr
    mpan
end
