include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "elrab2.mm"

theorem mapdordlem1
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cL: class L
  let cO: class O
  let cY: class Y
  assume mapdordlem1.t: |- T = { g e. F | ( O ` ( O ` ( L ` g ) ) ) e. Y }

  disjoint F g
  disjoint J g
  disjoint L g
  disjoint O g
  disjoint Y g
  assert |- ( J e. T <-> ( J e. F /\ ( O ` ( O ` ( L ` J ) ) ) e. Y ) )

  proof
    vg
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    #
    cY
    wcel
    cJ
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    #
    cY
    wcel
    vg
    cJ
    cF
    cT
    @0
    cJ
    wceq
    #
    @3
    @6
    cY
    @7
    @2
    @5
    cO
    @7
    @1
    @4
    cO
    @0
    cJ
    cL
    fveq2
    fveq2d
    fveq2d
    eleq1d
    mapdordlem1.t
    elrab2
end
