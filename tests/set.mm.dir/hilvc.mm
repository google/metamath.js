include "csm.mm"
include "cva.mm"
include "cop.mm"
include "chil.mm"
include "hilablo.mm"
include "cxp.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "ax-hfvmul.mm"
include "cv.mm"
include "ax-hvmulid.mm"
include "ax-hvdistr1.mm"
include "ax-hvdistr2.mm"
include "ax-hvmulass.mm"
include "eqid.mm"
include "isvciOLD.mm"

theorem hilvc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- <. +h , .h >. e. CVecOLD

  proof
    vx
    vy
    vz
    csm
    cva
    cva
    csm
    cop
    #
    chil
    hilablo
    chil
    chil
    cxp
    chil
    cva
    ax-hfvadd
    fdmi
    ax-hfvmul
    vx
    cv
    #
    ax-hvmulid
    vy
    cv
    #
    @1
    vz
    cv
    #
    ax-hvdistr1
    @2
    @3
    @1
    ax-hvdistr2
    @2
    @3
    @1
    ax-hvmulass
    @0
    eqid
    isvciOLD
end
