include "c0.mm"
include "wne.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cfil.mm"
include "cmetu.mm"
include "ccfilu.mm"
include "cv.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "ccfil.mm"
include "cpsmet.mm"
include "wb.mm"
include "xmetpsmet.mm"
include "cfbas.mm"
include "cfilucfil2.mm"
include "anbi2d.mm"
include "filfbas.mm"
include "pm4.71i.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "sylan2.mm"
include "iscfil.mm"
include "adantl.mm"
include "bitr4d.mm"

theorem cfilucfil3
  let cC: class C
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( X =/= (/) /\ D e. ( *Met ` X ) ) -> ( ( C e. ( Fil ` X ) /\ C e. ( CauFilU ` ( metUnif ` D ) ) ) <-> C e. ( CauFil ` D ) ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    wa
    cC
    cX
    cfil
    cfv
    wcel
    #
    cC
    cD
    cmetu
    cfv
    ccfilu
    cfv
    wcel
    #
    wa
    #
    @2
    cD
    vy
    cv
    #
    @5
    cxp
    cima
    cc0
    vx
    cv
    cico
    co
    wss
    vy
    cC
    wrex
    vx
    crp
    wral
    #
    wa
    #
    cC
    cD
    ccfil
    cfv
    wcel
    #
    @1
    @0
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    @4
    @7
    wb
    cD
    cX
    xmetpsmet
    @0
    @9
    wa
    #
    @4
    @2
    cC
    cX
    cfbas
    cfv
    wcel
    #
    @6
    wa
    #
    wa
    #
    @7
    @10
    @3
    @12
    @2
    vx
    vy
    cC
    cD
    cX
    cfilucfil2
    anbi2d
    @7
    @2
    @11
    wa
    #
    @6
    wa
    @13
    @2
    @14
    @6
    @2
    @11
    cC
    cX
    filfbas
    pm4.71i
    anbi1i
    @2
    @11
    @6
    anass
    bitr2i
    syl6bb
    sylan2
    @1
    @8
    @7
    wb
    @0
    vx
    vy
    cD
    cC
    cX
    iscfil
    adantl
    bitr4d
end
