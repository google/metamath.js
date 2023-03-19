include "cnq.mm"
include "wcel.mm"
include "ceq.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wmo.mm"
include "wceq.mm"
include "3simpa.mm"
include "wrmo.mm"
include "cnpi.mm"
include "cxp.mm"
include "wreu.mm"
include "elpqn.mm"
include "3ad2ant2.mm"
include "nqereu.mm"
include "reurmo.mm"
include "3syl.mm"
include "df-rmo.mm"
include "sylib.mm"
include "3simpb.mm"
include "simp2.mm"
include "wer.mm"
include "enqer.mm"
include "a1i.mm"
include "erref.mm"
include "jca.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "moi.mm"
include "syl112anc.mm"

theorem enqeq
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. Q. /\ B e. Q. /\ A ~Q B ) -> A = B )

  proof
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    cA
    cB
    ceq
    wbr
    #
    w3a
    #
    @0
    @1
    wa
    vx
    cv
    #
    cnq
    wcel
    #
    @4
    cB
    ceq
    wbr
    #
    wa
    #
    vx
    wmo
    #
    @0
    @2
    wa
    #
    @1
    cB
    cB
    ceq
    wbr
    #
    wa
    #
    cA
    cB
    wceq
    @0
    @1
    @2
    3simpa
    @3
    @6
    vx
    cnq
    wrmo
    #
    @8
    @3
    cB
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    @6
    vx
    cnq
    wreu
    @12
    @1
    @0
    @14
    @2
    cB
    elpqn
    3ad2ant2
    #
    vx
    cB
    nqereu
    @6
    vx
    cnq
    reurmo
    3syl
    @6
    vx
    cnq
    df-rmo
    sylib
    @0
    @1
    @2
    3simpb
    @3
    @1
    @10
    @0
    @1
    @2
    simp2
    @3
    cB
    ceq
    @13
    @13
    ceq
    wer
    @3
    enqer
    a1i
    @15
    erref
    jca
    @7
    @9
    @11
    vx
    cA
    cB
    cnq
    cnq
    @4
    cA
    wceq
    @5
    @0
    @6
    @2
    @4
    cA
    cnq
    eleq1
    @4
    cA
    cB
    ceq
    breq1
    anbi12d
    @4
    cB
    wceq
    @5
    @1
    @6
    @10
    @4
    cB
    cnq
    eleq1
    @4
    cB
    cB
    ceq
    breq1
    anbi12d
    moi
    syl112anc
end
