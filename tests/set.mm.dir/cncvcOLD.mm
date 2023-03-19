include "cmul.mm"
include "caddc.mm"
include "cop.mm"
include "cc.mm"
include "cnaddabloOLD.mm"
include "cxp.mm"
include "ax-addf.mm"
include "fdmi.mm"
include "ax-mulf.mm"
include "cv.mm"
include "mulid2.mm"
include "adddi.mm"
include "adddir.mm"
include "mulass.mm"
include "eqid.mm"
include "isvciOLD.mm"

theorem cncvcOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- <. + , x. >. e. CVecOLD

  proof
    vx
    vy
    vz
    cmul
    caddc
    caddc
    cmul
    cop
    #
    cc
    cnaddabloOLD
    cc
    cc
    cxp
    cc
    caddc
    ax-addf
    fdmi
    ax-mulf
    vx
    cv
    #
    mulid2
    vy
    cv
    #
    @1
    vz
    cv
    #
    adddi
    @2
    @3
    @1
    adddir
    @2
    @3
    @1
    mulass
    @0
    eqid
    isvciOLD
end
