include "cdm.mm"
include "wcel.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "cae.mm"
include "wbr.mm"
include "cdif.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "wa.mm"
include "simpr.mm"
include "dmeqd.mm"
include "unieqd.mm"
include "simpl.mm"
include "difeq12d.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "df-ae.mm"
include "brabga.mm"
include "ancoms.mm"

theorem brae
  let cA: class A
  let cM: class M
  let va: setvar a
  let vm: setvar m


  assert |- ( ( M e. U. ran measures /\ A e. dom M ) -> ( A ae M <-> ( M ` ( U. dom M \ A ) ) = 0 ) )

  proof
    cA
    cM
    cdm
    #
    wcel
    cM
    cmeas
    crn
    cuni
    #
    wcel
    cA
    cM
    cae
    wbr
    @0
    cuni
    #
    cA
    cdif
    #
    cM
    cfv
    #
    cc0
    wceq
    #
    wb
    vm
    cv
    #
    cdm
    #
    cuni
    #
    va
    cv
    #
    cdif
    #
    @6
    cfv
    #
    cc0
    wceq
    @5
    va
    vm
    cA
    cM
    cae
    @0
    @1
    @9
    cA
    wceq
    #
    @6
    cM
    wceq
    #
    wa
    #
    @11
    @4
    cc0
    @14
    @10
    @3
    @6
    cM
    @12
    @13
    simpr
    #
    @14
    @8
    @2
    @9
    cA
    @14
    @7
    @0
    @14
    @6
    cM
    @15
    dmeqd
    unieqd
    @12
    @13
    simpl
    difeq12d
    fveq12d
    eqeq1d
    vm
    va
    df-ae
    brabga
    ancoms
end
