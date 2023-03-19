include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "wss.mm"
include "chss.mm"
include "adantr.mm"
include "axpjcl.mm"
include "sseldd.mm"

theorem pjhcl
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( projh ` H ) ` A ) e. ~H )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    cH
    chil
    cA
    cH
    cpjh
    cfv
    cfv
    @0
    cH
    chil
    wss
    @1
    cH
    chss
    adantr
    cA
    cH
    axpjcl
    sseldd
end
