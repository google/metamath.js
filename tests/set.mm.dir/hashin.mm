include "wcel.mm"
include "cin.mm"
include "wss.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "inss1.mm"
include "hashss.mm"
include "mpan2.mm"

theorem hashin
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( # ` ( A i^i B ) ) <_ ( # ` A ) )

  proof
    cA
    cV
    wcel
    cA
    cB
    cin
    #
    cA
    wss
    @0
    chash
    cfv
    cA
    chash
    cfv
    cle
    wbr
    cA
    cB
    inss1
    cA
    @0
    cV
    hashss
    mpan2
end
