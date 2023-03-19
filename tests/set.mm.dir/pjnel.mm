include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wn.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "cif.mm"
include "c0v.mm"
include "wceq.mm"
include "eleq2.mm"
include "notbid.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "eleq1.mm"
include "breq12d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "pjneli.mm"
include "dedth2h.mm"

theorem pjnel
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( -. A e. H <-> ( normh ` ( ( projh ` H ) ` A ) ) < ( normh ` A ) ) )

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
    wcel
    #
    wn
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
    clt
    wbr
    #
    wb
    cA
    @0
    cH
    chil
    cif
    #
    wcel
    #
    wn
    #
    cA
    @9
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    @7
    clt
    wbr
    #
    wb
    @1
    cA
    c0v
    cif
    #
    @9
    wcel
    #
    wn
    #
    @16
    @12
    cfv
    #
    cno
    cfv
    #
    @16
    cno
    cfv
    #
    clt
    wbr
    #
    wb
    cH
    cA
    chil
    c0v
    cH
    @9
    wceq
    #
    @3
    @11
    @8
    @15
    @23
    @2
    @10
    cH
    @9
    cA
    eleq2
    notbid
    @23
    @6
    @14
    @7
    clt
    @23
    @5
    @13
    cno
    @23
    cA
    @4
    @12
    cH
    @9
    cpjh
    fveq2
    fveq1d
    fveq2d
    breq1d
    bibi12d
    cA
    @16
    wceq
    #
    @11
    @18
    @15
    @22
    @24
    @10
    @17
    cA
    @16
    @9
    eleq1
    notbid
    @24
    @14
    @20
    @7
    @21
    clt
    @24
    @13
    @19
    cno
    cA
    @16
    @12
    fveq2
    fveq2d
    cA
    @16
    cno
    fveq2
    breq12d
    bibi12d
    @16
    @9
    cH
    ifchhv
    cA
    ifhvhv0
    pjneli
    dedth2h
end
