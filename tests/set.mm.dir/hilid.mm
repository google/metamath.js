include "cva.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "crio.mm"
include "c0v.mm"
include "cgr.mm"
include "wcel.mm"
include "cablo.mm"
include "hilablo.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "grporn.mm"
include "eqid.mm"
include "grpoidval.mm"
include "hvaddid2.mm"
include "rgen.mm"
include "wreu.mm"
include "wb.mm"
include "ax-hv0cl.mm"
include "grpoideu.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqtri.mm"

theorem hilid
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( GId ` +h ) = 0h

  proof
    cva
    cgi
    cfv
    #
    vy
    cv
    #
    vx
    cv
    #
    cva
    co
    #
    @2
    wceq
    #
    vx
    chil
    wral
    #
    vy
    chil
    crio
    #
    c0v
    cva
    cgr
    wcel
    #
    @0
    @6
    wceq
    cva
    cablo
    wcel
    @7
    hilablo
    cva
    ablogrpo
    ax-mp
    #
    vx
    vy
    @0
    cva
    chil
    cva
    chil
    @8
    chil
    chil
    cxp
    chil
    cva
    ax-hfvadd
    fdmi
    grporn
    #
    @0
    eqid
    grpoidval
    ax-mp
    c0v
    @2
    cva
    co
    #
    @2
    wceq
    #
    vx
    chil
    wral
    #
    @6
    c0v
    wceq
    #
    @11
    vx
    chil
    @2
    hvaddid2
    rgen
    c0v
    chil
    wcel
    @5
    vy
    chil
    wreu
    #
    @12
    @13
    wb
    ax-hv0cl
    @7
    @14
    @8
    vx
    vy
    cva
    chil
    @9
    grpoideu
    ax-mp
    @5
    @12
    vy
    chil
    c0v
    @1
    c0v
    wceq
    #
    @4
    @11
    vx
    chil
    @15
    @3
    @10
    @2
    @1
    c0v
    @2
    cva
    oveq1
    eqeq1d
    ralbidv
    riota2
    mp2an
    mpbi
    eqtri
end
