include "cv.mm"
include "cep.mm"
include "wbr.mm"
include "cvv.mm"
include "cdif.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "copab.mm"
include "wss.mm"
include "cxp.mm"
include "cxrn.mm"
include "crn.mm"
include "cssr.mm"
include "wcel.mm"
include "epel.mm"
include "brvdif.mm"
include "xchbinx.mm"
include "anbi12i.mm"
include "exbii.mm"
include "notbii.mm"
include "dfss6.mm"
include "bitr4i.mm"
include "opabbii.mm"
include "rnxrn.mm"
include "difeq2i.mm"
include "vvdifopab.mm"
include "eqtri.mm"
include "df-ssr.mm"
include "3eqtr4ri.mm"

theorem dfssr2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- _S = ( ( _V X. _V ) \ ran ( _E |X. ( _V \ _E ) ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    cep
    wbr
    #
    @0
    vy
    cv
    #
    cvv
    cep
    cdif
    #
    wbr
    #
    wa
    #
    vz
    wex
    #
    wn
    #
    vx
    vy
    copab
    #
    @1
    @3
    wss
    #
    vx
    vy
    copab
    cvv
    cvv
    cxp
    #
    cep
    @4
    cxrn
    crn
    #
    cdif
    #
    cssr
    @8
    @10
    vx
    vy
    @8
    @0
    @1
    wcel
    #
    @0
    @3
    wcel
    #
    wn
    #
    wa
    #
    vz
    wex
    #
    wn
    @10
    @7
    @18
    @6
    @17
    vz
    @2
    @14
    @5
    @16
    vz
    vx
    epel
    @5
    @0
    @3
    cep
    wbr
    @15
    @0
    @3
    cep
    brvdif
    vz
    vy
    epel
    xchbinx
    anbi12i
    exbii
    notbii
    vz
    @1
    @3
    dfss6
    bitr4i
    opabbii
    @13
    @11
    @7
    vx
    vy
    copab
    #
    cdif
    @9
    @12
    @19
    @11
    vx
    vy
    vz
    cep
    @4
    rnxrn
    difeq2i
    @7
    vx
    vy
    vvdifopab
    eqtri
    vx
    vy
    df-ssr
    3eqtr4ri
end
