include "cbigcup.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "relbigcup.mm"
include "brrelexi.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "uniexb.mm"
include "sylibr.mm"
include "cv.mm"
include "breq1.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "cxp.mm"
include "cep.mm"
include "ccom.mm"
include "vex.mm"
include "df-bigcup.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "wrex.mm"
include "epel.mm"
include "rexbii.mm"
include "coep.mm"
include "eluni2.mm"
include "3bitr4ri.mm"
include "brtxpsd3.mm"
include "eqcom.mm"
include "bitri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem brbigcup
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume brbigcup.1: |- B e. _V


  assert |- ( A Bigcup B <-> U. A = B )

  proof
    cA
    cB
    cbigcup
    wbr
    #
    cA
    cvv
    wcel
    #
    cA
    cuni
    #
    cB
    wceq
    #
    cA
    cB
    cbigcup
    relbigcup
    brrelexi
    @3
    @2
    cvv
    wcel
    #
    @1
    @3
    @4
    cB
    cvv
    wcel
    #
    brbigcup.1
    @2
    cB
    cvv
    eleq1
    mpbiri
    cA
    uniexb
    sylibr
    vx
    cv
    #
    cB
    cbigcup
    wbr
    #
    @6
    cuni
    #
    cB
    wceq
    #
    @0
    @3
    vx
    cA
    cvv
    @6
    cA
    cB
    cbigcup
    breq1
    @6
    cA
    wceq
    @8
    @2
    cB
    @6
    cA
    unieq
    eqeq1d
    @7
    cB
    @8
    wceq
    @9
    vy
    @6
    cB
    cvv
    cvv
    cxp
    #
    cbigcup
    cep
    cep
    ccom
    #
    @8
    vx
    vex
    #
    brbigcup.1
    df-bigcup
    @6
    cB
    @10
    wbr
    @6
    cvv
    wcel
    @5
    @12
    brbigcup.1
    @6
    cB
    cvv
    cvv
    brxp
    mpbir2an
    vy
    cv
    #
    vz
    cv
    #
    cep
    wbr
    #
    vz
    @6
    wrex
    @13
    @14
    wcel
    #
    vz
    @6
    wrex
    @13
    @6
    @11
    wbr
    @13
    @8
    wcel
    @15
    @16
    vz
    @6
    vy
    vz
    epel
    rexbii
    vz
    @13
    @6
    cep
    vy
    vex
    @12
    coep
    vz
    @13
    @6
    eluni2
    3bitr4ri
    brtxpsd3
    cB
    @8
    eqcom
    bitri
    vtoclbg
    pm5.21nii
end
