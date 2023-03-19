include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c0v.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "ifhvhv0.mm"
include "norm3adifii.mm"
include "dedth2h.mm"

theorem norm3adifi
  let cA: class A
  let cB: class B
  let cC: class C
  assume norm3adift.1: |- C e. ~H


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( abs ` ( ( normh ` ( A -h C ) ) - ( normh ` ( B -h C ) ) ) ) <_ ( normh ` ( A -h B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cB
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    #
    cle
    wbr
    @0
    cA
    c0v
    cif
    #
    cC
    cmv
    co
    #
    cno
    cfv
    #
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    cB
    cmv
    co
    #
    cno
    cfv
    #
    cle
    wbr
    @12
    @1
    cB
    c0v
    cif
    #
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    @17
    cmv
    co
    #
    cno
    cfv
    #
    cle
    wbr
    cA
    cB
    c0v
    c0v
    cA
    @10
    wceq
    #
    @7
    @14
    @9
    @16
    cle
    @24
    @6
    @13
    cabs
    @24
    @3
    @12
    @5
    cmin
    @24
    @2
    @11
    cno
    cA
    @10
    cC
    cmv
    oveq1
    fveq2d
    oveq1d
    fveq2d
    @24
    @8
    @15
    cno
    cA
    @10
    cB
    cmv
    oveq1
    fveq2d
    breq12d
    cB
    @17
    wceq
    #
    @14
    @21
    @16
    @23
    cle
    @25
    @13
    @20
    cabs
    @25
    @5
    @19
    @12
    cmin
    @25
    @4
    @18
    cno
    cB
    @17
    cC
    cmv
    oveq1
    fveq2d
    oveq2d
    fveq2d
    @25
    @15
    @22
    cno
    cB
    @17
    @10
    cmv
    oveq2
    fveq2d
    breq12d
    @10
    @17
    cC
    cA
    ifhvhv0
    cB
    ifhvhv0
    norm3adift.1
    norm3adifii
    dedth2h
end
