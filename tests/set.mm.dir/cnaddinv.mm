include "cc.mm"
include "wcel.mm"
include "cminusg.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "negid.mm"
include "cgrp.mm"
include "wb.mm"
include "cabl.mm"
include "cnaddabl.mm"
include "ablgrp.mm"
include "ax-mp.mm"
include "id.mm"
include "negcl.mm"
include "cvv.mm"
include "cbs.mm"
include "cnex.mm"
include "grpbase.mm"
include "cplusg.mm"
include "addex.mm"
include "grpplusg.mm"
include "c0g.mm"
include "cnaddid.mm"
include "eqcomi.mm"
include "eqid.mm"
include "grpinvid1.mm"
include "mp3an2i.mm"
include "mpbird.mm"

theorem cnaddinv
  let cA: class A
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnaddabl.g: |- G = { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. }


  assert |- ( A e. CC -> ( ( invg ` G ) ` A ) = -u A )

  proof
    cA
    cc
    wcel
    #
    cA
    cG
    cminusg
    cfv
    #
    cfv
    cA
    cneg
    #
    wceq
    #
    cA
    @2
    caddc
    co
    cc0
    wceq
    #
    cA
    negid
    cG
    cgrp
    wcel
    #
    @0
    @0
    @2
    cc
    wcel
    @3
    @4
    wb
    cG
    cabl
    wcel
    @5
    cG
    cnaddabl.g
    cnaddabl
    cG
    ablgrp
    ax-mp
    @0
    id
    cA
    negcl
    cc
    caddc
    cG
    @1
    cA
    @2
    cc0
    cc
    cvv
    wcel
    cc
    cG
    cbs
    cfv
    wceq
    cnex
    cc
    caddc
    cG
    cvv
    cnaddabl.g
    grpbase
    ax-mp
    caddc
    cvv
    wcel
    caddc
    cG
    cplusg
    cfv
    wceq
    addex
    cc
    caddc
    cG
    cvv
    cnaddabl.g
    grpplusg
    ax-mp
    cG
    c0g
    cfv
    cc0
    cG
    cnaddabl.g
    cnaddid
    eqcomi
    @1
    eqid
    grpinvid1
    mp3an2i
    mpbird
end
