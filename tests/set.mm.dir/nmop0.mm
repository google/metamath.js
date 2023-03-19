include "ch0o.mm"
include "cnop.mm"
include "cfv.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cc0.mm"
include "csn.mm"
include "wf.mm"
include "ho0f.mm"
include "nmopval.mm"
include "ax-mp.mm"
include "wcel.mm"
include "c0v.mm"
include "ho0val.mm"
include "fveq2d.mm"
include "norm0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbiia.mm"
include "ax-hv0cl.mm"
include "0le1.mm"
include "fveq2.mm"
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

theorem nmop0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( normop ` 0hop ) = 0

  proof
    ch0o
    cnop
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
    @1
    ch0o
    cfv
    #
    cno
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
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    chil
    chil
    ch0o
    wf
    @0
    @11
    wceq
    ho0f
    vx
    vy
    ch0o
    nmopval
    ax-mp
    cxr
    @10
    @12
    clt
    @10
    @4
    cc0
    wceq
    #
    vx
    cab
    @12
    @9
    @14
    vx
    @9
    @3
    @14
    wa
    #
    vy
    chil
    wrex
    #
    @14
    @8
    @15
    vy
    chil
    @1
    chil
    wcel
    #
    @7
    @14
    @3
    @17
    @6
    cc0
    @4
    @17
    @6
    c0v
    cno
    cfv
    #
    cc0
    @17
    @5
    c0v
    cno
    @1
    ho0val
    fveq2d
    norm0
    syl6eq
    eqeq2d
    anbi2d
    rexbiia
    @16
    @3
    vy
    chil
    wrex
    #
    @14
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
    @3
    @20
    vy
    c0v
    chil
    @1
    c0v
    wceq
    #
    @2
    cc0
    c1
    cle
    @21
    @2
    @18
    cc0
    @1
    c0v
    cno
    fveq2
    norm0
    syl6eq
    breq1d
    rspcev
    mp2an
    @3
    @14
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
    @13
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
