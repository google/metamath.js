include "cop.mm"
include "ccom.mm"
include "wcel.mm"
include "wbr.mm"
include "csn.mm"
include "cima.mm"
include "df-br.mm"
include "cvv.mm"
include "wa.mm"
include "wrel.mm"
include "relco.mm"
include "brrelex12.mm"
include "mpan.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "snprc.mm"
include "noel.mm"
include "imaeq2.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "imaeq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "sylbi.mm"
include "con4i.mm"
include "elex.mm"
include "jca.mm"
include "cv.mm"
include "wex.mm"
include "wrex.mm"
include "df-rex.mm"
include "wb.mm"
include "vex.mm"
include "elimasng.mm"
include "mpan2.mm"
include "syl6bbr.mm"
include "adantr.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5rbb.mm"
include "brcog.mm"
include "elimag.mm"
include "adantl.mm"
include "3bitr4d.mm"
include "pm5.21nii.mm"
include "bitr3i.mm"

theorem opelco3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z


  assert |- ( <. A , B >. e. ( C o. D ) <-> B e. ( C " ( D " { A } ) ) )

  proof
    cA
    cB
    cop
    cC
    cD
    ccom
    #
    wcel
    cA
    cB
    @0
    wbr
    #
    cB
    cC
    cD
    cA
    csn
    #
    cima
    #
    cima
    #
    wcel
    #
    cA
    cB
    @0
    df-br
    @1
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    @5
    @0
    wrel
    @1
    @8
    cC
    cD
    relco
    cA
    cB
    @0
    brrelex12
    mpan
    @5
    @6
    @7
    @6
    @5
    @6
    wn
    @2
    c0
    wceq
    #
    @5
    wn
    cA
    snprc
    @9
    @5
    cB
    c0
    wcel
    cB
    noel
    @9
    @4
    c0
    cB
    @9
    @4
    cC
    cD
    c0
    cima
    #
    cima
    #
    c0
    @9
    @3
    @10
    cC
    @2
    c0
    cD
    imaeq2
    imaeq2d
    @11
    cC
    c0
    cima
    c0
    @10
    c0
    cC
    cD
    ima0
    imaeq2i
    cC
    ima0
    eqtri
    syl6eq
    eleq2d
    mtbiri
    sylbi
    con4i
    cB
    @4
    elex
    jca
    @8
    cA
    vz
    cv
    #
    cD
    wbr
    #
    @12
    cB
    cC
    wbr
    #
    wa
    #
    vz
    wex
    #
    @14
    vz
    @3
    wrex
    #
    @1
    @5
    @17
    @12
    @3
    wcel
    #
    @14
    wa
    #
    vz
    wex
    @8
    @16
    @14
    vz
    @3
    df-rex
    @8
    @19
    @15
    vz
    @8
    @18
    @13
    @14
    @6
    @18
    @13
    wb
    @7
    @6
    @18
    cA
    @12
    cop
    cD
    wcel
    #
    @13
    @6
    @12
    cvv
    wcel
    @18
    @20
    wb
    vz
    vex
    cD
    cA
    @12
    cvv
    cvv
    elimasng
    mpan2
    cA
    @12
    cD
    df-br
    syl6bbr
    adantr
    anbi1d
    exbidv
    syl5rbb
    vz
    cA
    cB
    cC
    cD
    cvv
    cvv
    brcog
    @7
    @5
    @17
    wb
    @6
    vz
    cB
    cC
    @3
    cvv
    elimag
    adantl
    3bitr4d
    pm5.21nii
    bitr3i
end
