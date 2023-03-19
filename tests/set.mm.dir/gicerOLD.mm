include "cgrp.mm"
include "cgic.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "cxp.mm"
include "wss.mm"
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
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "gicsym.mm"
include "adantl.mm"
include "wa.mm"
include "gictr.mm"
include "wcel.mm"
include "wb.mm"
include "gicref.mm"
include "giclcl.mm"
include "impbii.mm"
include "iserd.mm"
include "trud.mm"

theorem gicerOLD
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
    cgrp
    cgic
    wer
    wtru
    vx
    vy
    vz
    cgrp
    cgic
    cgic
    wrel
    #
    wtru
    cgic
    cgrp
    cgrp
    cxp
    #
    wss
    @1
    wrel
    @0
    cgic
    cgim
    ccnv
    cvv
    c1o
    cdif
    #
    cima
    #
    @1
    df-gic
    @3
    cgim
    cdm
    #
    @1
    cgim
    @2
    cnvimass
    cgim
    @1
    wfn
    @4
    @1
    wceq
    gimfn
    @1
    cgim
    fndm
    ax-mp
    sseqtri
    eqsstri
    cgrp
    cgrp
    relxp
    cgic
    @1
    relss
    mp2
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cgic
    wbr
    #
    @6
    @5
    cgic
    wbr
    wtru
    @5
    @6
    gicsym
    adantl
    @7
    @6
    vz
    cv
    #
    cgic
    wbr
    wa
    @5
    @8
    cgic
    wbr
    wtru
    @5
    @6
    @8
    gictr
    adantl
    @5
    cgrp
    wcel
    #
    @5
    @5
    cgic
    wbr
    #
    wb
    wtru
    @9
    @10
    @5
    gicref
    @5
    @5
    giclcl
    impbii
    a1i
    iserd
    trud
end
