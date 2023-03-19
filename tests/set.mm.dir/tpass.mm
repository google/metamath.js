include "ctp.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "tprot.mm"
include "uncom.mm"
include "3eqtr4i.mm"

theorem tpass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { A , B , C } = ( { A } u. { B , C } )

  proof
    cB
    cC
    cA
    ctp
    cB
    cC
    cpr
    #
    cA
    csn
    #
    cun
    cA
    cB
    cC
    ctp
    @1
    @0
    cun
    cB
    cC
    cA
    df-tp
    cA
    cB
    cC
    tprot
    @1
    @0
    uncom
    3eqtr4i
end
