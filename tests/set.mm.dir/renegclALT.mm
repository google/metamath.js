include "cv.mm"
include "cneg.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "negeq.mm"
include "eleq1d.mm"
include "cc0.mm"
include "cif.mm"
include "wsbc.mm"
include "csb.mm"
include "cvv.mm"
include "vex.mm"
include "c0ex.mm"
include "ifex.mm"
include "csbnegg.mm"
include "ax-mp.mm"
include "csbvarg.mm"
include "0re.mm"
include "eqeltri.mm"
include "wb.mm"
include "sbcel1g.mm"
include "mpbir.mm"
include "elimhyps.mm"
include "mpbi.mm"
include "renegcli.mm"
include "dedths.mm"
include "vtoclga.mm"

theorem renegclALT
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR -> -u A e. RR )

  proof
    vx
    cv
    #
    cneg
    #
    cr
    wcel
    #
    cA
    cneg
    #
    cr
    wcel
    vx
    cA
    cr
    @0
    cA
    wceq
    @1
    @3
    cr
    @0
    cA
    negeq
    eleq1d
    @0
    cr
    wcel
    #
    @2
    vx
    cc0
    @2
    vx
    @4
    @0
    cc0
    cif
    #
    wsbc
    #
    vx
    @5
    @1
    csb
    #
    cr
    wcel
    #
    @7
    vx
    @5
    @0
    csb
    #
    cneg
    #
    cr
    @5
    cvv
    wcel
    #
    @7
    @10
    wceq
    @4
    @0
    cc0
    vx
    vex
    c0ex
    ifex
    #
    vx
    @5
    @0
    cvv
    csbnegg
    ax-mp
    @9
    @4
    vx
    @5
    wsbc
    #
    @9
    cr
    wcel
    #
    @4
    vx
    cc0
    @4
    vx
    cc0
    wsbc
    #
    vx
    cc0
    @0
    csb
    #
    cr
    wcel
    #
    @16
    cc0
    cr
    cc0
    cvv
    wcel
    #
    @16
    cc0
    wceq
    c0ex
    vx
    cc0
    cvv
    csbvarg
    ax-mp
    0re
    eqeltri
    @18
    @15
    @17
    wb
    c0ex
    vx
    cc0
    @0
    cr
    cvv
    sbcel1g
    ax-mp
    mpbir
    elimhyps
    @11
    @13
    @14
    wb
    @12
    vx
    @5
    @0
    cr
    cvv
    sbcel1g
    ax-mp
    mpbi
    renegcli
    eqeltri
    @11
    @6
    @8
    wb
    @12
    vx
    @5
    @1
    cr
    cvv
    sbcel1g
    ax-mp
    mpbir
    dedths
    vtoclga
end
