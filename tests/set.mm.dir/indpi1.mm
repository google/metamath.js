include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cind.mm"
include "cfv.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "ind1a.mm"
include "3expia.mm"
include "pm5.32d.mm"
include "cc0.mm"
include "cpr.mm"
include "wf.mm"
include "wfn.mm"
include "indf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3syl.mm"
include "ssel.mm"
include "pm4.71rd.mm"
include "adantl.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem indpi1
  let cA: class A
  let cO: class O
  let cV: class V
  let vx: setvar x


  assert |- ( ( O e. V /\ A C_ O ) -> ( `' ( ( _Ind ` O ) ` A ) " { 1 } ) = A )

  proof
    cO
    cV
    wcel
    #
    cA
    cO
    wss
    #
    wa
    #
    vx
    cA
    cO
    cind
    cfv
    cfv
    #
    ccnv
    c1
    csn
    cima
    #
    cA
    @2
    vx
    cv
    #
    cO
    wcel
    #
    @5
    @3
    cfv
    c1
    wceq
    #
    wa
    #
    @6
    @5
    cA
    wcel
    #
    wa
    #
    @5
    @4
    wcel
    #
    @9
    @2
    @6
    @7
    @9
    @0
    @1
    @6
    @7
    @9
    wb
    cA
    cO
    cV
    @5
    ind1a
    3expia
    pm5.32d
    @2
    cO
    cc0
    c1
    cpr
    #
    @3
    wf
    @3
    cO
    wfn
    @11
    @8
    wb
    cA
    cO
    cV
    indf
    cO
    @12
    @3
    ffn
    cO
    c1
    @5
    @3
    fniniseg
    3syl
    @1
    @9
    @10
    wb
    @0
    @1
    @9
    @6
    cA
    cO
    @5
    ssel
    pm4.71rd
    adantl
    3bitr4d
    eqrdv
end
