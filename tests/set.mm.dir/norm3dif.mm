include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "c0v.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "ifhvhv0.mm"
include "norm3difi.mm"
include "dedth3h.mm"

theorem norm3dif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( normh ` ( A -h B ) ) <_ ( ( normh ` ( A -h C ) ) + ( normh ` ( C -h B ) ) ) )

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
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    #
    cA
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cC
    cB
    cmv
    co
    #
    cno
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    @0
    cA
    c0v
    cif
    #
    cB
    cmv
    co
    #
    cno
    cfv
    #
    @10
    cC
    cmv
    co
    #
    cno
    cfv
    #
    @8
    caddc
    co
    #
    cle
    wbr
    @10
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    cno
    cfv
    #
    @14
    cC
    @16
    cmv
    co
    #
    cno
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    @18
    @10
    @2
    cC
    c0v
    cif
    #
    cmv
    co
    #
    cno
    cfv
    #
    @22
    @16
    cmv
    co
    #
    cno
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    cA
    cB
    cC
    c0v
    c0v
    c0v
    cA
    @10
    wceq
    #
    @4
    @12
    @9
    @15
    cle
    @28
    @3
    @11
    cno
    cA
    @10
    cB
    cmv
    oveq1
    fveq2d
    @28
    @6
    @14
    @8
    caddc
    @28
    @5
    @13
    cno
    cA
    @10
    cC
    cmv
    oveq1
    fveq2d
    oveq1d
    breq12d
    cB
    @16
    wceq
    #
    @12
    @18
    @15
    @21
    cle
    @29
    @11
    @17
    cno
    cB
    @16
    @10
    cmv
    oveq2
    fveq2d
    @29
    @8
    @20
    @14
    caddc
    @29
    @7
    @19
    cno
    cB
    @16
    cC
    cmv
    oveq2
    fveq2d
    oveq2d
    breq12d
    cC
    @22
    wceq
    #
    @21
    @27
    @18
    cle
    @30
    @14
    @24
    @20
    @26
    caddc
    @30
    @13
    @23
    cno
    cC
    @22
    @10
    cmv
    oveq2
    fveq2d
    @30
    @19
    @25
    cno
    cC
    @22
    @16
    cmv
    oveq1
    fveq2d
    oveq12d
    breq2d
    @10
    @16
    @22
    cA
    ifhvhv0
    cB
    ifhvhv0
    cC
    ifhvhv0
    norm3difi
    dedth3h
end
