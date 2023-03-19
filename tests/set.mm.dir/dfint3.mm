include "cint.mm"
include "wel.mm"
include "wral.mm"
include "cab.mm"
include "cvv.mm"
include "cep.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "dfint2.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "wcel.mm"
include "ralnex.mm"
include "vex.mm"
include "brcnv.mm"
include "brv.mm"
include "brdif.mm"
include "mpbiran.mm"
include "bitr2i.mm"
include "con1bii.mm"
include "epel.mm"
include "ralbii.mm"
include "eldif.mm"
include "elima.mm"
include "xchbinx.mm"
include "3bitr4ri.mm"
include "abbi2i.mm"
include "eqtr4i.mm"

theorem dfint3
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- |^| A = ( _V \ ( `' ( _V \ _E ) " A ) )

  proof
    cA
    cint
    vx
    vy
    wel
    #
    vy
    cA
    wral
    #
    vx
    cab
    cvv
    cvv
    cep
    cdif
    #
    ccnv
    #
    cA
    cima
    #
    cdif
    #
    vx
    vy
    cA
    dfint2
    @1
    vx
    @5
    vy
    cv
    #
    vx
    cv
    #
    @3
    wbr
    #
    wn
    #
    vy
    cA
    wral
    @8
    vy
    cA
    wrex
    #
    wn
    @1
    @7
    @5
    wcel
    #
    @8
    vy
    cA
    ralnex
    @0
    @9
    vy
    cA
    @9
    @7
    @6
    cep
    wbr
    #
    @0
    @12
    @8
    @8
    @7
    @6
    @2
    wbr
    #
    @12
    wn
    #
    @6
    @7
    @2
    vy
    vex
    vx
    vex
    #
    brcnv
    @13
    @7
    @6
    cvv
    wbr
    @14
    @7
    @6
    brv
    @7
    @6
    cvv
    cep
    brdif
    mpbiran
    bitr2i
    con1bii
    vx
    vy
    epel
    bitr2i
    ralbii
    @11
    @7
    @4
    wcel
    #
    @10
    @11
    @7
    cvv
    wcel
    @16
    wn
    @15
    @7
    cvv
    @4
    eldif
    mpbiran
    vy
    @7
    @3
    cA
    @15
    elima
    xchbinx
    3bitr4ri
    abbi2i
    eqtr4i
end
