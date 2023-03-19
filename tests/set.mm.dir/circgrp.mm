include "cabl.mm"
include "wcel.mm"
include "wtru.mm"
include "ci.mm"
include "cr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cress.mm"
include "crn.mm"
include "wfo.mm"
include "efifo.mm"
include "forn.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "csubg.mm"
include "csubrg.mm"
include "crefld.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "efabl.mm"
include "trud.mm"

theorem circgrp
  let cC: class C
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume circgrp.1: |- C = ( `' abs " { 1 } )
  assume circgrp.2: |- T = ( ( mulGrp ` CCfld ) |`s C )


  assert |- T e. Abel

  proof
    cT
    cabl
    wcel
    wtru
    vy
    ci
    vx
    cr
    ci
    vx
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmpt
    #
    cT
    cr
    vx
    vy
    cr
    @2
    ci
    vy
    cv
    #
    cmul
    co
    #
    ce
    cfv
    @0
    @4
    wceq
    @1
    @5
    ce
    @0
    @4
    ci
    cmul
    oveq2
    fveq2d
    cbvmptv
    #
    cT
    ccnfld
    cmgp
    cfv
    #
    cC
    cress
    co
    @7
    @3
    crn
    #
    cress
    co
    circgrp.2
    cC
    @8
    @7
    cress
    @8
    cC
    cr
    cC
    @3
    wfo
    @8
    cC
    wceq
    vy
    cC
    @3
    @6
    circgrp.1
    efifo
    cr
    cC
    @3
    forn
    ax-mp
    eqcomi
    oveq2i
    eqtri
    ci
    cc
    wcel
    wtru
    ax-icn
    a1i
    cr
    ccnfld
    csubg
    cfv
    wcel
    #
    wtru
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @9
    @10
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    ccnfld
    subrgsubg
    ax-mp
    a1i
    efabl
    trud
end
