include "wfun.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "cdm.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "funfn.mm"
include "cfv.mm"
include "wa.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "fvres.mm"
include "eleq1d.mm"
include "adantl.mm"
include "pm5.32i.mm"
include "a1i.mm"
include "an32.mm"
include "syl6bb.mm"
include "wceq.mm"
include "fnfun.mm"
include "funres.mm"
include "syl.mm"
include "dmres.mm"
include "jctir.mm"
include "df-fn.mm"
include "sylibr.mm"
include "elpreima.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "sylbi.mm"
include "eqrdv.mm"

theorem respreima
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( Fun F -> ( `' ( F |` B ) " A ) = ( ( `' F " A ) i^i B ) )

  proof
    cF
    wfun
    #
    vx
    cF
    cB
    cres
    #
    ccnv
    cA
    cima
    #
    cF
    ccnv
    cA
    cima
    #
    cB
    cin
    #
    @0
    cF
    cF
    cdm
    #
    wfn
    #
    vx
    cv
    #
    @2
    wcel
    #
    @7
    @4
    wcel
    #
    wb
    cF
    funfn
    @6
    @7
    cB
    @5
    cin
    #
    wcel
    #
    @7
    @1
    cfv
    #
    cA
    wcel
    #
    wa
    #
    @7
    @5
    wcel
    #
    @7
    cF
    cfv
    #
    cA
    wcel
    #
    wa
    #
    @7
    cB
    wcel
    #
    wa
    #
    @8
    @9
    @6
    @14
    @15
    @19
    wa
    #
    @17
    wa
    #
    @20
    @14
    @22
    wb
    @6
    @14
    @21
    @13
    wa
    @22
    @11
    @21
    @13
    @11
    @19
    @15
    wa
    @21
    @7
    cB
    @5
    elin
    @19
    @15
    ancom
    bitri
    anbi1i
    @21
    @13
    @17
    @19
    @13
    @17
    wb
    @15
    @19
    @12
    @16
    cA
    @7
    cB
    cF
    fvres
    eleq1d
    adantl
    pm5.32i
    bitri
    a1i
    @15
    @19
    @17
    an32
    syl6bb
    @6
    @1
    @10
    wfn
    #
    @8
    @14
    wb
    @6
    @1
    wfun
    #
    @1
    cdm
    @10
    wceq
    #
    wa
    @23
    @6
    @24
    @25
    @6
    @0
    @24
    @5
    cF
    fnfun
    cB
    cF
    funres
    syl
    cF
    cB
    dmres
    jctir
    @1
    @10
    df-fn
    sylibr
    @10
    @7
    cA
    @1
    elpreima
    syl
    @9
    @7
    @3
    wcel
    #
    @19
    wa
    @6
    @20
    @7
    @3
    cB
    elin
    @6
    @26
    @18
    @19
    @5
    @7
    cA
    cF
    elpreima
    anbi1d
    syl5bb
    3bitr4d
    sylbi
    eqrdv
end
