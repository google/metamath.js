include "cnp.mm"
include "cltp.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wpss.mm"
include "pssirr.mm"
include "ltprord.mm"
include "mtbiri.mm"
include "anidms.mm"
include "w3a.mm"
include "wi.mm"
include "psstr.mm"
include "wb.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3adant2.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "weq.mm"
include "w3o.mm"
include "psslinpr.mm"
include "biidd.mm"
include "ancoms.mm"
include "3orbi123d.mm"
include "mpbird.mm"
include "issoi.mm"

theorem ltsopr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- <P Or P.

  proof
    vx
    vy
    vz
    cnp
    cltp
    vx
    cv
    #
    cnp
    wcel
    #
    @0
    @0
    cltp
    wbr
    #
    wn
    @1
    @1
    wa
    @2
    @0
    @0
    wpss
    @0
    pssirr
    @0
    @0
    ltprord
    mtbiri
    anidms
    @1
    vy
    cv
    #
    cnp
    wcel
    #
    vz
    cv
    #
    cnp
    wcel
    #
    w3a
    #
    @0
    @3
    cltp
    wbr
    #
    @3
    @5
    cltp
    wbr
    #
    wa
    #
    @0
    @5
    cltp
    wbr
    #
    wi
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
    @0
    @3
    @5
    psstr
    @7
    @10
    @14
    @11
    @15
    @7
    @8
    @12
    @9
    @13
    @1
    @4
    @8
    @12
    wb
    @6
    @0
    @3
    ltprord
    #
    3adant3
    @4
    @6
    @9
    @13
    wb
    @1
    @3
    @5
    ltprord
    3adant1
    anbi12d
    @1
    @6
    @11
    @15
    wb
    @4
    @0
    @5
    ltprord
    3adant2
    imbi12d
    mpbiri
    @1
    @4
    wa
    #
    @8
    vx
    vy
    weq
    #
    @3
    @0
    cltp
    wbr
    #
    w3o
    @12
    @18
    @3
    @0
    wpss
    #
    w3o
    @0
    @3
    psslinpr
    @17
    @8
    @12
    @18
    @18
    @19
    @20
    @16
    @17
    @18
    biidd
    @4
    @1
    @19
    @20
    wb
    @3
    @0
    ltprord
    ancoms
    3orbi123d
    mpbird
    issoi
end
