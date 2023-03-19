include "cm1r.mm"
include "c1r.mm"
include "cplr.mm"
include "co.mm"
include "c1p.mm"
include "cpp.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "c0r.mm"
include "df-m1r.mm"
include "df-1r.mm"
include "oveq12i.mm"
include "df-0r.mm"
include "cnp.mm"
include "wcel.mm"
include "wceq.mm"
include "1pr.mm"
include "addclpr.mm"
include "mp2an.mm"
include "addsrpr.mm"
include "mp4an.mm"
include "addasspr.mm"
include "oveq2i.mm"
include "wb.mm"
include "enreceq.mm"
include "mpbir.mm"
include "eqtr4i.mm"

theorem m1p1sr



  assert |- ( -1R +R 1R ) = 0R

  proof
    cm1r
    c1r
    cplr
    co
    c1p
    c1p
    c1p
    cpp
    co
    #
    cop
    cer
    cec
    #
    @0
    c1p
    cop
    cer
    cec
    #
    cplr
    co
    #
    c0r
    cm1r
    @1
    c1r
    @2
    cplr
    df-m1r
    df-1r
    oveq12i
    c0r
    c1p
    c1p
    cop
    cer
    cec
    #
    @3
    df-0r
    @3
    c1p
    @0
    cpp
    co
    #
    @0
    c1p
    cpp
    co
    #
    cop
    cer
    cec
    #
    @4
    c1p
    cnp
    wcel
    #
    @0
    cnp
    wcel
    #
    @9
    @8
    @3
    @7
    wceq
    1pr
    @8
    @8
    @9
    1pr
    1pr
    c1p
    c1p
    addclpr
    mp2an
    #
    @10
    1pr
    c1p
    @0
    @0
    c1p
    addsrpr
    mp4an
    @4
    @7
    wceq
    #
    c1p
    @6
    cpp
    co
    c1p
    @5
    cpp
    co
    wceq
    #
    @6
    @5
    c1p
    cpp
    c1p
    c1p
    c1p
    addasspr
    oveq2i
    @8
    @8
    @5
    cnp
    wcel
    #
    @6
    cnp
    wcel
    #
    @11
    @12
    wb
    1pr
    1pr
    @8
    @9
    @13
    1pr
    @10
    c1p
    @0
    addclpr
    mp2an
    @9
    @8
    @14
    @10
    1pr
    @0
    c1p
    addclpr
    mp2an
    c1p
    c1p
    @5
    @6
    enreceq
    mp4an
    mpbir
    eqtr4i
    eqtr4i
    eqtr4i
end
