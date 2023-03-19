include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "congid.mm"
include "orcd.mm"

theorem acongid
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A || ( B - B ) \/ A || ( B - -u B ) ) )

  proof
    cA
    cz
    wcel
    cB
    cz
    wcel
    wa
    cA
    cB
    cB
    cmin
    co
    cdvds
    wbr
    cA
    cB
    cB
    cneg
    cmin
    co
    cdvds
    wbr
    cA
    cB
    congid
    orcd
end
