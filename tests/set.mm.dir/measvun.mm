include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wdisj.mm"
include "wa.mm"
include "w3a.mm"
include "cuni.mm"
include "cesum.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "simp2.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "csiga.mm"
include "crn.mm"
include "wb.mm"
include "measbase.mm"
include "ismeas.mm"
include "syl.mm"
include "ibi.mm"
include "simp3d.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "breq1.mm"
include "disjeq1.mm"
include "anbi12d.mm"
include "unieq.mm"
include "fveq2d.mm"
include "esumeq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem measvun
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cM: class M
  let vy: setvar y

  disjoint A x
  disjoint M x
  disjoint x y
  disjoint A y
  disjoint M y
  disjoint S y
  assert |- ( ( M e. ( measures ` S ) /\ A e. ~P S /\ ( A ~<_ _om /\ Disj_ x e. A x ) ) -> ( M ` U. A ) = sum* x e. A ( M ` x ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cA
    cS
    cpw
    #
    wcel
    #
    cA
    com
    cdom
    wbr
    #
    vx
    cA
    vx
    cv
    #
    wdisj
    #
    wa
    #
    w3a
    @2
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    @7
    @4
    wdisj
    #
    wa
    #
    @7
    cuni
    #
    cM
    cfv
    #
    @7
    @4
    cM
    cfv
    #
    vx
    cesum
    #
    wceq
    #
    wi
    #
    vy
    @1
    wral
    #
    @6
    cA
    cuni
    #
    cM
    cfv
    #
    cA
    @13
    vx
    cesum
    #
    wceq
    #
    @0
    @2
    @6
    simp2
    @0
    @2
    @17
    @6
    @0
    cS
    cc0
    cpnf
    cicc
    co
    cM
    wf
    #
    c0
    cM
    cfv
    cc0
    wceq
    #
    @17
    @0
    @22
    @23
    @17
    w3a
    #
    @0
    cS
    csiga
    crn
    cuni
    wcel
    @0
    @24
    wb
    cS
    cM
    measbase
    vy
    vx
    cS
    cM
    ismeas
    syl
    ibi
    simp3d
    3ad2ant1
    @0
    @2
    @6
    simp3
    @16
    @6
    @21
    wi
    vy
    cA
    @1
    @7
    cA
    wceq
    #
    @10
    @6
    @15
    @21
    @25
    @8
    @3
    @9
    @5
    @7
    cA
    com
    cdom
    breq1
    vx
    @7
    cA
    @4
    disjeq1
    anbi12d
    @25
    @12
    @19
    @14
    @20
    @25
    @11
    @18
    cM
    @7
    cA
    unieq
    fveq2d
    @7
    cA
    @13
    vx
    esumeq1
    eqeq12d
    imbi12d
    rspcv
    syl3c
end
