include "caddc.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wral.mm"
include "crio.mm"
include "cc0.mm"
include "cgr.mm"
include "wcel.mm"
include "cablo.mm"
include "cnaddabloOLD.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-addf.mm"
include "fdmi.mm"
include "grporn.mm"
include "eqid.mm"
include "grpoidval.mm"
include "addid2.mm"
include "rgen.mm"
include "wreu.mm"
include "wb.mm"
include "0cn.mm"
include "grpoideu.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqtr2i.mm"

theorem cnidOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- 0 = ( GId ` + )

  proof
    caddc
    cgi
    cfv
    #
    vy
    cv
    #
    vx
    cv
    #
    caddc
    co
    #
    @2
    wceq
    #
    vx
    cc
    wral
    #
    vy
    cc
    crio
    #
    cc0
    caddc
    cgr
    wcel
    #
    @0
    @6
    wceq
    caddc
    cablo
    wcel
    @7
    cnaddabloOLD
    caddc
    ablogrpo
    ax-mp
    #
    vx
    vy
    @0
    caddc
    cc
    caddc
    cc
    @8
    cc
    cc
    cxp
    cc
    caddc
    ax-addf
    fdmi
    grporn
    #
    @0
    eqid
    grpoidval
    ax-mp
    cc0
    @2
    caddc
    co
    #
    @2
    wceq
    #
    vx
    cc
    wral
    #
    @6
    cc0
    wceq
    #
    @11
    vx
    cc
    @2
    addid2
    rgen
    cc0
    cc
    wcel
    @5
    vy
    cc
    wreu
    #
    @12
    @13
    wb
    0cn
    @7
    @14
    @8
    vx
    vy
    caddc
    cc
    @9
    grpoideu
    ax-mp
    @5
    @12
    vy
    cc
    cc0
    @1
    cc0
    wceq
    #
    @4
    @11
    vx
    cc
    @15
    @3
    @10
    @2
    @1
    cc0
    @2
    caddc
    oveq1
    eqeq1d
    ralbidv
    riota2
    mp2an
    mpbi
    eqtr2i
end
