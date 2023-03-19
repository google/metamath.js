include "ci.mm"
include "cc.mm"
include "wcel.mm"
include "c0r.mm"
include "cnr.mm"
include "c1r.mm"
include "0r.mm"
include "1sr.mm"
include "cop.mm"
include "wa.mm"
include "df-i.mm"
include "eleq1i.mm"
include "opelcn.mm"
include "bitri.mm"
include "mpbir2an.mm"

theorem axicn



  assert |- _i e. CC

  proof
    ci
    cc
    wcel
    #
    c0r
    cnr
    wcel
    #
    c1r
    cnr
    wcel
    #
    0r
    1sr
    @0
    c0r
    c1r
    cop
    #
    cc
    wcel
    @1
    @2
    wa
    ci
    @3
    cc
    df-i
    eleq1i
    c0r
    c1r
    opelcn
    bitri
    mpbir2an
end
