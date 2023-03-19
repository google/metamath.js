include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "shss.mm"
include "ocorth.mm"
include "syl.mm"

theorem shocorth
  let cA: class A
  let cB: class B
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( H e. SH -> ( ( A e. H /\ B e. ( _|_ ` H ) ) -> ( A .ih B ) = 0 ) )

  proof
    cH
    csh
    wcel
    cH
    chil
    wss
    cA
    cH
    wcel
    cB
    cH
    cort
    cfv
    wcel
    wa
    cA
    cB
    csp
    co
    cc0
    wceq
    wi
    cH
    shss
    cA
    cB
    cH
    ocorth
    syl
end
