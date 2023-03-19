include "chil.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cnmf.mm"
include "cfv.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "clf.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "0lnfn.mm"
include "lnfnf.mm"
include "nmfnval.mm"
include "mp2b.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "fveq2d.mm"
include "abs0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbiia.mm"
include "c0v.mm"
include "ax-hv0cl.mm"
include "0le1.mm"
include "fveq2.mm"
include "norm0.mm"
include "breq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "r19.41v.mm"
include "mpbiran.mm"
include "bitri.mm"
include "abbii.mm"
include "df-sn.mm"
include "eqtr4i.mm"
include "supeq1i.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "3eqtri.mm"

theorem nmfn0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( normfn ` ( ~H X. { 0 } ) ) = 0

  proof
    chil
    cc0
    csn
    #
    cxp
    #
    cnmf
    cfv
    #
    vy
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @3
    @1
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    @0
    cxr
    clt
    csup
    #
    cc0
    @1
    clf
    wcel
    chil
    cc
    @1
    wf
    @2
    @13
    wceq
    0lnfn
    @1
    lnfnf
    vx
    vy
    @1
    nmfnval
    mp2b
    cxr
    @12
    @0
    clt
    @12
    @6
    cc0
    wceq
    #
    vx
    cab
    @0
    @11
    @15
    vx
    @11
    @5
    @15
    wa
    #
    vy
    chil
    wrex
    #
    @15
    @10
    @16
    vy
    chil
    @3
    chil
    wcel
    #
    @9
    @15
    @5
    @18
    @8
    cc0
    @6
    @18
    @8
    cc0
    cabs
    cfv
    cc0
    @18
    @7
    cc0
    cabs
    chil
    cc0
    @3
    c0ex
    fvconst2
    fveq2d
    abs0
    syl6eq
    eqeq2d
    anbi2d
    rexbiia
    @17
    @5
    vy
    chil
    wrex
    #
    @15
    c0v
    chil
    wcel
    cc0
    c1
    cle
    wbr
    #
    @19
    ax-hv0cl
    0le1
    @5
    @20
    vy
    c0v
    chil
    @3
    c0v
    wceq
    #
    @4
    cc0
    c1
    cle
    @21
    @4
    c0v
    cno
    cfv
    cc0
    @3
    c0v
    cno
    fveq2
    norm0
    syl6eq
    breq1d
    rspcev
    mp2an
    @5
    @15
    vy
    chil
    r19.41v
    mpbiran
    bitri
    abbii
    vx
    cc0
    df-sn
    eqtr4i
    supeq1i
    cxr
    clt
    wor
    cc0
    cxr
    wcel
    @14
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    3eqtri
end
