include "ctgp.mm"
include "crg.mm"
include "cin.mm"
include "wcel.mm"
include "ctmd.mm"
include "wa.mm"
include "ctrg.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "cmgp.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "df-trg.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem istrg
  let cR: class R
  let cM: class M
  let vr: setvar r
  let cU: class U
  assume istrg.1: |- M = ( mulGrp ` R )


  assert |- ( R e. TopRing <-> ( R e. TopGrp /\ R e. Ring /\ M e. TopMnd ) )

  proof
    cR
    ctgp
    crg
    cin
    #
    wcel
    #
    cM
    ctmd
    wcel
    #
    wa
    cR
    ctgp
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    @2
    wa
    cR
    ctrg
    wcel
    @3
    @4
    @2
    w3a
    @1
    @5
    @2
    cR
    ctgp
    crg
    elin
    anbi1i
    vr
    cv
    #
    cmgp
    cfv
    #
    ctmd
    wcel
    @2
    vr
    cR
    @0
    ctrg
    @6
    cR
    wceq
    #
    @7
    cM
    ctmd
    @8
    @7
    cR
    cmgp
    cfv
    cM
    @6
    cR
    cmgp
    fveq2
    istrg.1
    syl6eqr
    eleq1d
    vr
    df-trg
    elrab2
    @3
    @4
    @2
    df-3an
    3bitr4i
end
