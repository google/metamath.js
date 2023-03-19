include "c0r.mm"
include "c1r.mm"
include "cop.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ci.mm"
include "c1.mm"
include "cc0.mm"
include "cm1r.mm"
include "cplr.mm"
include "cmr.mm"
include "cnr.mm"
include "wcel.mm"
include "wceq.mm"
include "0r.mm"
include "1sr.mm"
include "mulcnsr.mm"
include "mp4an.mm"
include "00sr.mm"
include "ax-mp.mm"
include "1idsr.mm"
include "oveq2i.mm"
include "m1r.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "addcomsr.mm"
include "0idsr.mm"
include "3eqtri.mm"
include "opeq12i.mm"
include "oveq1i.mm"
include "addresr.mm"
include "mp2an.mm"
include "m1p1sr.mm"
include "opeq1i.mm"
include "df-i.mm"
include "df-1.mm"
include "df-0.mm"
include "3eqtr4i.mm"

theorem axi2m1



  assert |- ( ( _i x. _i ) + 1 ) = 0

  proof
    c0r
    c1r
    cop
    #
    @0
    cmul
    co
    #
    c1r
    c0r
    cop
    #
    caddc
    co
    #
    c0r
    c0r
    cop
    #
    ci
    ci
    cmul
    co
    #
    c1
    caddc
    co
    cc0
    @3
    cm1r
    c0r
    cop
    #
    @2
    caddc
    co
    #
    cm1r
    c1r
    cplr
    co
    #
    c0r
    cop
    #
    @4
    @1
    @6
    @2
    caddc
    @1
    c0r
    c0r
    cmr
    co
    #
    cm1r
    c1r
    c1r
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    #
    c1r
    c0r
    cmr
    co
    #
    c0r
    c1r
    cmr
    co
    #
    cplr
    co
    #
    cop
    #
    @6
    c0r
    cnr
    wcel
    #
    c1r
    cnr
    wcel
    #
    @18
    @19
    @1
    @17
    wceq
    0r
    1sr
    0r
    1sr
    c0r
    c1r
    c0r
    c1r
    mulcnsr
    mp4an
    @13
    cm1r
    @16
    c0r
    @13
    c0r
    cm1r
    cplr
    co
    cm1r
    c0r
    cplr
    co
    #
    cm1r
    @10
    c0r
    @12
    cm1r
    cplr
    @18
    @10
    c0r
    wceq
    0r
    c0r
    00sr
    ax-mp
    @12
    cm1r
    c1r
    cmr
    co
    #
    cm1r
    @11
    c1r
    cm1r
    cmr
    @19
    @11
    c1r
    wceq
    1sr
    c1r
    1idsr
    ax-mp
    oveq2i
    cm1r
    cnr
    wcel
    #
    @21
    cm1r
    wceq
    m1r
    cm1r
    1idsr
    ax-mp
    eqtri
    oveq12i
    c0r
    cm1r
    addcomsr
    @22
    @20
    cm1r
    wceq
    m1r
    cm1r
    0idsr
    ax-mp
    3eqtri
    @16
    c0r
    c0r
    cplr
    co
    #
    c0r
    @14
    c0r
    @15
    c0r
    cplr
    @19
    @14
    c0r
    wceq
    1sr
    c1r
    00sr
    ax-mp
    @18
    @15
    c0r
    wceq
    0r
    c0r
    1idsr
    ax-mp
    oveq12i
    @18
    @23
    c0r
    wceq
    0r
    c0r
    0idsr
    ax-mp
    eqtri
    opeq12i
    eqtri
    oveq1i
    @22
    @19
    @7
    @9
    wceq
    m1r
    1sr
    cm1r
    c1r
    addresr
    mp2an
    @8
    c0r
    c0r
    m1p1sr
    opeq1i
    3eqtri
    @5
    @1
    c1
    @2
    caddc
    ci
    @0
    ci
    @0
    cmul
    df-i
    df-i
    oveq12i
    df-1
    oveq12i
    df-0
    3eqtr4i
end
