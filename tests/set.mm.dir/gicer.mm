include "cgrp.mm"
include "cgic.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "cgim.mm"
include "ccnv.mm"
include "cvv.mm"
include "c1o.mm"
include "cdif.mm"
include "cima.mm"
include "df-gic.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "wceq.mm"
include "gimfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "cv.mm"
include "gicsym.mm"
include "gictr.mm"
include "wcel.mm"
include "wbr.mm"
include "gicref.mm"
include "giclcl.mm"
include "impbii.mm"
include "iseri.mm"

theorem gicer
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let cC: class C
  let vg: setvar g
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ~=g Er Grp

  proof
    vx
    vy
    vz
    cgrp
    cgic
    cgic
    cgrp
    cgrp
    cxp
    #
    wss
    @0
    wrel
    cgic
    wrel
    cgic
    cgim
    ccnv
    cvv
    c1o
    cdif
    #
    cima
    #
    @0
    df-gic
    @2
    cgim
    cdm
    #
    @0
    cgim
    @1
    cnvimass
    cgim
    @0
    wfn
    @3
    @0
    wceq
    gimfn
    @0
    cgim
    fndm
    ax-mp
    sseqtri
    eqsstri
    cgrp
    cgrp
    relxp
    cgic
    @0
    relss
    mp2
    vx
    cv
    #
    vy
    cv
    #
    gicsym
    @4
    @5
    vz
    cv
    gictr
    @4
    cgrp
    wcel
    @4
    @4
    cgic
    wbr
    @4
    gicref
    @4
    @4
    giclcl
    impbii
    iseri
end
