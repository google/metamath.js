include "c0.mm"
include "wne.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "cmetu.mm"
include "ccfilu.mm"
include "ccfil.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "cfilucfil3.mm"
include "cfilfil.mm"
include "ex.mm"
include "adantl.mm"
include "pm4.71rd.mm"
include "bitrd.mm"
include "pm5.32.mm"
include "sylibr.mm"
include "3impia.mm"

theorem cfilucfil4
  let cC: class C
  let cD: class D
  let cX: class X


  assert |- ( ( X =/= (/) /\ D e. ( *Met ` X ) /\ C e. ( Fil ` X ) ) -> ( C e. ( CauFilU ` ( metUnif ` D ) ) <-> C e. ( CauFil ` D ) ) )

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
    cC
    cD
    ccfil
    cfv
    wcel
    #
    wb
    #
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    @2
    @4
    wa
    #
    wb
    @2
    @5
    wi
    @6
    @7
    @4
    @8
    cC
    cD
    cX
    cfilucfil3
    @6
    @4
    @2
    @1
    @4
    @2
    wi
    @0
    @1
    @4
    @2
    cD
    cC
    cX
    cfilfil
    ex
    adantl
    pm4.71rd
    bitrd
    @2
    @3
    @4
    pm5.32
    sylibr
    3impia
end
