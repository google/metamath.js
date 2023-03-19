include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "c0v.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "breq12d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "pjnormi.mm"
include "dedth2h.mm"

theorem pjnorm
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( normh ` ( ( projh ` H ) ` A ) ) <_ ( normh ` A ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    cA
    cno
    cfv
    #
    cle
    wbr
    cA
    @0
    cH
    chil
    cif
    #
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    @5
    cle
    wbr
    @1
    cA
    c0v
    cif
    #
    @7
    cfv
    #
    cno
    cfv
    #
    @10
    cno
    cfv
    #
    cle
    wbr
    cH
    cA
    chil
    c0v
    cH
    @6
    wceq
    #
    @4
    @9
    @5
    cle
    @14
    @3
    @8
    cno
    @14
    cA
    @2
    @7
    cH
    @6
    cpjh
    fveq2
    fveq1d
    fveq2d
    breq1d
    cA
    @10
    wceq
    #
    @9
    @12
    @5
    @13
    cle
    @15
    @8
    @11
    cno
    cA
    @10
    @7
    fveq2
    fveq2d
    cA
    @10
    cno
    fveq2
    breq12d
    @10
    @6
    cH
    ifchhv
    cA
    ifhvhv0
    pjnormi
    dedth2h
end
