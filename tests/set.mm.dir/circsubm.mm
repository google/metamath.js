include "cr.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "csubmnd.mm"
include "wfo.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "efifo.mm"
include "forn.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "wcel.mm"
include "wtru.mm"
include "cress.mm"
include "oveq2i.mm"
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
include "efsubm.mm"
include "trud.mm"
include "eqeltri.mm"

theorem circsubm
  let cC: class C
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume circgrp.1: |- C = ( `' abs " { 1 } )
  assume circgrp.2: |- T = ( ( mulGrp ` CCfld ) |`s C )


  assert |- C e. ( SubMnd ` ( mulGrp ` CCfld ) )

  proof
    cC
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
    crn
    #
    ccnfld
    cmgp
    cfv
    #
    csubmnd
    cfv
    #
    @4
    cC
    cr
    cC
    @3
    wfo
    @4
    cC
    wceq
    vy
    cC
    @3
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
    @7
    wceq
    @1
    @8
    ce
    @0
    @7
    ci
    cmul
    oveq2
    fveq2d
    cbvmptv
    #
    circgrp.1
    efifo
    cr
    cC
    @3
    forn
    ax-mp
    eqcomi
    #
    @4
    @6
    wcel
    wtru
    vy
    ci
    @3
    @5
    cC
    cress
    co
    cr
    @9
    cC
    @4
    @5
    cress
    @10
    oveq2i
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
    @11
    @12
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
    efsubm
    trud
    eqeltri
end
