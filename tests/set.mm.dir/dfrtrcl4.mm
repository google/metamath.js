include "crtcl.mm"
include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "cmpt.mm"
include "cc0.mm"
include "ctcl.mm"
include "cfv.mm"
include "cun.mm"
include "dfrtrcl3.mm"
include "wcel.mm"
include "csn.mm"
include "cn.mm"
include "wceq.mm"
include "df-n0.mm"
include "equncomi.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iunxun.mm"
include "eqtri.mm"
include "c0ex.mm"
include "oveq2.mm"
include "iunxsn.mm"
include "a1i.mm"
include "weq.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "dftrcl3.mm"
include "nnex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "mpteq2ia.mm"

theorem dfrtrcl4
  let vr: setvar r
  let vn: setvar n
  let vx: setvar x


  assert |- t* = ( r e. _V |-> ( ( r ^r 0 ) u. ( t+ ` r ) ) )

  proof
    crtcl
    vr
    cvv
    vn
    cn0
    vr
    cv
    #
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
    cvv
    @0
    cc0
    crelexp
    co
    #
    @0
    ctcl
    cfv
    #
    cun
    #
    cmpt
    vn
    vr
    dfrtrcl3
    vr
    cvv
    @3
    @6
    @0
    cvv
    wcel
    #
    @3
    vn
    cc0
    csn
    #
    @2
    ciun
    #
    vn
    cn
    @2
    ciun
    #
    cun
    #
    @6
    @3
    vn
    @8
    cn
    cun
    #
    @2
    ciun
    #
    @11
    cn0
    @12
    wceq
    @3
    @13
    wceq
    cn0
    cn
    @8
    df-n0
    equncomi
    vn
    cn0
    @12
    @2
    iuneq1
    ax-mp
    vn
    @8
    cn
    @2
    iunxun
    eqtri
    @7
    @9
    @4
    @10
    @5
    @9
    @4
    wceq
    @7
    vn
    cc0
    @2
    @4
    c0ex
    @1
    cc0
    @0
    crelexp
    oveq2
    iunxsn
    a1i
    @7
    @5
    @10
    vx
    @0
    vn
    cn
    vx
    cv
    #
    @1
    crelexp
    co
    #
    ciun
    @10
    cvv
    ctcl
    vx
    vr
    weq
    vn
    cn
    @15
    @2
    @14
    @0
    @1
    crelexp
    oveq1
    iuneq2d
    vn
    vx
    dftrcl3
    vn
    cn
    @2
    nnex
    @0
    @1
    crelexp
    ovex
    iunex
    fvmpt
    eqcomd
    uneq12d
    syl5eq
    mpteq2ia
    eqtri
end
