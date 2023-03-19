include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "dvds0.mm"
include "adantr.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "subidd.mm"
include "breqtrrd.mm"

theorem congid
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> A || ( B - B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cc0
    cB
    cB
    cmin
    co
    cdvds
    @0
    cA
    cc0
    cdvds
    wbr
    @1
    cA
    dvds0
    adantr
    @2
    cB
    @1
    cB
    cc
    wcel
    @0
    cB
    zcn
    adantl
    subidd
    breqtrrd
end
