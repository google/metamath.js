include "cz.mm"
include "crefld.mm"
include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "csubg.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "cr.mm"
include "wral.mm"
include "csubrg.mm"
include "ccnfld.mm"
include "wss.mm"
include "zsubrg.mm"
include "zssre.mm"
include "wa.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "df-refld.mm"
include "subsubrg.mm"
include "ax-mp.mm"
include "mpbir2an.mm"
include "subrgsubg.mm"
include "simpl.mm"
include "recnd.mm"
include "simpr.mm"
include "addcomd.mm"
include "eleq1d.mm"
include "rgen2a.mm"
include "rebase.mm"
include "replusg.mm"
include "isnsg.mm"
include "qusgrp.mm"

theorem rzgrp
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume rzgrp.r: |- R = ( RRfld /s ( RRfld ~QG ZZ ) )


  assert |- R e. Grp

  proof
    cz
    crefld
    cnsg
    cfv
    wcel
    #
    cR
    cgrp
    wcel
    @0
    cz
    crefld
    csubg
    cfv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    cz
    wcel
    @3
    @2
    caddc
    co
    #
    cz
    wcel
    wb
    #
    vy
    cr
    wral
    vx
    cr
    wral
    cz
    crefld
    csubrg
    cfv
    wcel
    #
    @1
    @7
    cz
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    cz
    cr
    wss
    #
    zsubrg
    zssre
    cr
    @8
    wcel
    #
    @7
    @9
    @10
    wa
    wb
    @11
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    cz
    ccnfld
    crefld
    df-refld
    subsubrg
    ax-mp
    mpbir2an
    cz
    crefld
    subrgsubg
    ax-mp
    @6
    vx
    vy
    cr
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    wa
    #
    @4
    @5
    cz
    @14
    @2
    @3
    @14
    @2
    @12
    @13
    simpl
    recnd
    @14
    @3
    @12
    @13
    simpr
    recnd
    addcomd
    eleq1d
    rgen2a
    vx
    vy
    caddc
    cz
    crefld
    cr
    rebase
    replusg
    isnsg
    mpbir2an
    cz
    crefld
    cR
    rzgrp.r
    qusgrp
    ax-mp
end
