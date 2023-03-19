include "chil.mm"
include "wcel.mm"
include "cva.mm"
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
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifhvhv0.mm"
include "norm-ii-i.mm"
include "dedth2h.mm"

theorem norm-ii
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( normh ` ( A +h B ) ) <_ ( ( normh ` A ) + ( normh ` B ) ) )

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
    cB
    cva
    co
    #
    cno
    cfv
    #
    cA
    cno
    cfv
    #
    cB
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
    cva
    co
    #
    cno
    cfv
    #
    @7
    cno
    cfv
    #
    @5
    caddc
    co
    #
    cle
    wbr
    @7
    @1
    cB
    c0v
    cif
    #
    cva
    co
    #
    cno
    cfv
    #
    @10
    @12
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
    c0v
    c0v
    cA
    @7
    wceq
    #
    @3
    @9
    @6
    @11
    cle
    @17
    @2
    @8
    cno
    cA
    @7
    cB
    cva
    oveq1
    fveq2d
    @17
    @4
    @10
    @5
    caddc
    cA
    @7
    cno
    fveq2
    oveq1d
    breq12d
    cB
    @12
    wceq
    #
    @9
    @14
    @11
    @16
    cle
    @18
    @8
    @13
    cno
    cB
    @12
    @7
    cva
    oveq2
    fveq2d
    @18
    @5
    @15
    @10
    caddc
    cB
    @12
    cno
    fveq2
    oveq2d
    breq12d
    @7
    @12
    cA
    ifhvhv0
    cB
    ifhvhv0
    norm-ii-i
    dedth2h
end
