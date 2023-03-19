include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cin.mm"
include "crn.mm"
include "wcel.mm"
include "cz.mm"
include "wfn.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "cpw.mm"
include "wf.mm"
include "uzf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fvelrnb.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ineq2.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "uzin.mm"
include "ifcl.mm"
include "ancoms.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "2gencl.mm"

theorem uzin2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ran ZZ>= /\ B e. ran ZZ>= ) -> ( A i^i B ) e. ran ZZ>= )

  proof
    vx
    cv
    #
    cuz
    cfv
    #
    vy
    cv
    #
    cuz
    cfv
    #
    cin
    #
    cuz
    crn
    #
    wcel
    cA
    @3
    cin
    #
    @5
    wcel
    cA
    cB
    cin
    #
    @5
    wcel
    vx
    vy
    @1
    @3
    cA
    cB
    cz
    @5
    cuz
    cz
    wfn
    #
    cA
    @5
    wcel
    @1
    cA
    wceq
    #
    vx
    cz
    wrex
    wb
    cz
    cz
    cpw
    #
    cuz
    wf
    @8
    uzf
    cz
    @10
    cuz
    ffn
    ax-mp
    #
    vx
    cz
    cA
    cuz
    fvelrnb
    ax-mp
    @8
    cB
    @5
    wcel
    @3
    cB
    wceq
    #
    vy
    cz
    wrex
    wb
    @11
    vy
    cz
    cB
    cuz
    fvelrnb
    ax-mp
    @9
    @4
    @6
    @5
    @1
    cA
    @3
    ineq1
    eleq1d
    @12
    @6
    @7
    @5
    @3
    cB
    cA
    ineq2
    eleq1d
    @0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    @4
    @0
    @2
    cle
    wbr
    #
    @2
    @0
    cif
    #
    cuz
    cfv
    #
    @5
    @0
    @2
    uzin
    @15
    @8
    @17
    cz
    wcel
    #
    @18
    @5
    wcel
    @11
    @14
    @13
    @19
    @16
    @2
    @0
    cz
    ifcl
    ancoms
    cz
    @17
    cuz
    fnfvelrn
    sylancr
    eqeltrd
    2gencl
end
