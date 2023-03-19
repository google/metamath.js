include "ctrg.mm"
include "cdr.mm"
include "cin.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "ctgp.mm"
include "wa.mm"
include "ctdrg.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "cmgp.mm"
include "cfv.mm"
include "cui.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "df-tdrg.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem istdrg
  let cR: class R
  let cU: class U
  let cM: class M
  let vr: setvar r
  assume istrg.1: |- M = ( mulGrp ` R )
  assume istdrg.1: |- U = ( Unit ` R )


  assert |- ( R e. TopDRing <-> ( R e. TopRing /\ R e. DivRing /\ ( M |`s U ) e. TopGrp ) )

  proof
    cR
    ctrg
    cdr
    cin
    #
    wcel
    #
    cM
    cU
    cress
    co
    #
    ctgp
    wcel
    #
    wa
    cR
    ctrg
    wcel
    #
    cR
    cdr
    wcel
    #
    wa
    #
    @3
    wa
    cR
    ctdrg
    wcel
    @4
    @5
    @3
    w3a
    @1
    @6
    @3
    cR
    ctrg
    cdr
    elin
    anbi1i
    vr
    cv
    #
    cmgp
    cfv
    #
    @7
    cui
    cfv
    #
    cress
    co
    #
    ctgp
    wcel
    @3
    vr
    cR
    @0
    ctdrg
    @7
    cR
    wceq
    #
    @10
    @2
    ctgp
    @11
    @8
    cM
    @9
    cU
    cress
    @11
    @8
    cR
    cmgp
    cfv
    cM
    @7
    cR
    cmgp
    fveq2
    istrg.1
    syl6eqr
    @11
    @9
    cR
    cui
    cfv
    cU
    @7
    cR
    cui
    fveq2
    istdrg.1
    syl6eqr
    oveq12d
    eleq1d
    vr
    df-tdrg
    elrab2
    @4
    @5
    @3
    df-3an
    3bitr4i
end
