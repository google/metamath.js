include "ccnfld.mm"
include "cgrp.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "grpass.mm"
include "mpan.mm"

theorem cnncvsaddassdemo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )

  proof
    ccnfld
    cgrp
    wcel
    #
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    w3a
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    cA
    cB
    cC
    caddc
    co
    caddc
    co
    wceq
    ccnfld
    crg
    wcel
    @0
    cnring
    ccnfld
    ringgrp
    ax-mp
    cc
    caddc
    ccnfld
    cA
    cB
    cC
    cnfldbas
    cnfldadd
    grpass
    mpan
end
