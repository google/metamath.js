include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "neeq1.mm"
include "id.mm"
include "unieq.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "imbi12d.mm"
include "cpw.mm"
include "cvv.mm"
include "cin.mm"
include "crab.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "wf1.mm"
include "eqid.mm"
include "inf3lem6.mm"
include "vpwex.mm"
include "f1dom.mm"
include "csdm.mm"
include "wn.mm"
include "cfn.mm"
include "wcel.mm"
include "pwfi.mm"
include "biimpi.mm"
include "isfinite.mm"
include "3imtr3i.mm"
include "con3i.mm"
include "domtriom.mm"
include "vex.mm"
include "3imtr4i.mm"
include "3syl.mm"
include "vtocl.mm"

theorem dominf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assume dominf.1: |- A e. _V


  assert |- ( ( A =/= (/) /\ A C_ U. A ) -> _om ~<_ A )

  proof
    vx
    cv
    #
    c0
    wne
    #
    @0
    @0
    cuni
    #
    wss
    #
    wa
    #
    com
    @0
    cdom
    wbr
    #
    wi
    cA
    c0
    wne
    #
    cA
    cA
    cuni
    #
    wss
    #
    wa
    #
    com
    cA
    cdom
    wbr
    #
    wi
    vx
    cA
    dominf.1
    @0
    cA
    wceq
    #
    @4
    @9
    @5
    @10
    @11
    @1
    @6
    @3
    @8
    @0
    cA
    c0
    neeq1
    @11
    @0
    cA
    @2
    @7
    @11
    id
    @0
    cA
    unieq
    sseq12d
    anbi12d
    @0
    cA
    com
    cdom
    breq2
    imbi12d
    @4
    com
    @0
    cpw
    #
    vy
    cvv
    vw
    cv
    @0
    cin
    vy
    cv
    wss
    vw
    @0
    crab
    cmpt
    #
    c0
    crdg
    com
    cres
    #
    wf1
    com
    @12
    cdom
    wbr
    #
    @5
    vx
    vy
    vw
    cA
    cA
    @14
    @13
    @13
    eqid
    @14
    eqid
    dominf.1
    dominf.1
    inf3lem6
    com
    @12
    @14
    vx
    vpwex
    #
    f1dom
    @12
    com
    csdm
    wbr
    #
    wn
    @0
    com
    csdm
    wbr
    #
    wn
    @15
    @5
    @18
    @17
    @0
    cfn
    wcel
    #
    @12
    cfn
    wcel
    #
    @18
    @17
    @19
    @20
    @0
    pwfi
    biimpi
    @0
    isfinite
    @12
    isfinite
    3imtr3i
    con3i
    @12
    @16
    domtriom
    @0
    vx
    vex
    domtriom
    3imtr4i
    3syl
    vtocl
end
