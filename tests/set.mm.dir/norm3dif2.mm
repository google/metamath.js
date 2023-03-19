include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "norm3dif.mm"
include "wceq.mm"
include "normsub.mm"
include "3adant2.mm"
include "oveq1d.mm"
include "breqtrd.mm"

theorem norm3dif2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( normh ` ( A -h B ) ) <_ ( ( normh ` ( C -h A ) ) + ( normh ` ( C -h B ) ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    cA
    cB
    cmv
    co
    cno
    cfv
    cA
    cC
    cmv
    co
    cno
    cfv
    #
    cC
    cB
    cmv
    co
    cno
    cfv
    #
    caddc
    co
    cC
    cA
    cmv
    co
    cno
    cfv
    #
    @5
    caddc
    co
    cle
    cA
    cB
    cC
    norm3dif
    @3
    @4
    @6
    @5
    caddc
    @0
    @2
    @4
    @6
    wceq
    @1
    cA
    cC
    normsub
    3adant2
    oveq1d
    breqtrd
end
