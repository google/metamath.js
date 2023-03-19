include "crcl.mm"
include "cvv.mm"
include "cv.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "c1.mm"
include "cun.mm"
include "cmpt.mm"
include "cpr.mm"
include "ciun.mm"
include "dfrcl3.mm"
include "csn.mm"
include "wceq.mm"
include "df-pr.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iunxun.mm"
include "c0ex.mm"
include "oveq2.mm"
include "iunxsn.mm"
include "1ex.mm"
include "uneq12i.mm"
include "3eqtri.mm"
include "mpteq2i.mm"
include "eqtr4i.mm"

theorem dfrcl4
  let vn: setvar n
  let vr: setvar r

  disjoint n r
  assert |- r* = ( r e. _V |-> U_ n e. { 0 , 1 } ( r ^r n ) )

  proof
    crcl
    vr
    cvv
    vr
    cv
    #
    cc0
    crelexp
    co
    #
    @0
    c1
    crelexp
    co
    #
    cun
    #
    cmpt
    vr
    cvv
    vn
    cc0
    c1
    cpr
    #
    @0
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cmpt
    vr
    dfrcl3
    vr
    cvv
    @7
    @3
    @7
    vn
    cc0
    csn
    #
    c1
    csn
    #
    cun
    #
    @6
    ciun
    #
    vn
    @8
    @6
    ciun
    #
    vn
    @9
    @6
    ciun
    #
    cun
    @3
    @4
    @10
    wceq
    @7
    @11
    wceq
    cc0
    c1
    df-pr
    vn
    @4
    @10
    @6
    iuneq1
    ax-mp
    vn
    @8
    @9
    @6
    iunxun
    @12
    @1
    @13
    @2
    vn
    cc0
    @6
    @1
    c0ex
    @5
    cc0
    @0
    crelexp
    oveq2
    iunxsn
    vn
    c1
    @6
    @2
    1ex
    @5
    c1
    @0
    crelexp
    oveq2
    iunxsn
    uneq12i
    3eqtri
    mpteq2i
    eqtr4i
end
