include "crpss.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wpss.mm"
include "pssirr.mm"
include "psstr.mm"
include "vex.mm"
include "brrpss.mm"
include "notbii.mm"
include "anbi12i.mm"
include "imbi12i.mm"
include "mpbir2an.mm"
include "rgenw.mm"
include "rgen2w.mm"
include "df-po.mm"
include "mpbir.mm"

theorem porpss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- [C.] Po A

  proof
    cA
    crpss
    wpo
    vx
    cv
    #
    @0
    crpss
    wbr
    #
    wn
    #
    @0
    vy
    cv
    #
    crpss
    wbr
    #
    @3
    vz
    cv
    #
    crpss
    wbr
    #
    wa
    #
    @0
    @5
    crpss
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @11
    vx
    vy
    cA
    cA
    @10
    vz
    cA
    @10
    @0
    @0
    wpss
    #
    wn
    #
    @0
    @3
    wpss
    #
    @3
    @5
    wpss
    #
    wa
    #
    @0
    @5
    wpss
    #
    wi
    #
    @0
    pssirr
    @0
    @3
    @5
    psstr
    @2
    @13
    @9
    @18
    @1
    @12
    @0
    @0
    vx
    vex
    brrpss
    notbii
    @7
    @16
    @8
    @17
    @4
    @14
    @6
    @15
    @0
    @3
    vy
    vex
    brrpss
    @3
    @5
    vz
    vex
    #
    brrpss
    anbi12i
    @0
    @5
    @19
    brrpss
    imbi12i
    anbi12i
    mpbir2an
    rgenw
    rgen2w
    vx
    vy
    vz
    cA
    crpss
    df-po
    mpbir
end
