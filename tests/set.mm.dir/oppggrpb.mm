include "cgrp.mm"
include "wcel.mm"
include "oppggrp.mm"
include "coppg.mm"
include "cfv.mm"
include "eqid.mm"
include "wb.mm"
include "wtru.mm"
include "cbs.mm"
include "wceq.mm"
include "oppgbas.mm"
include "a1i.mm"
include "eqidd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wa.mm"
include "oppgplus.mm"
include "eqtri.mm"
include "grppropd.mm"
include "trud.mm"
include "sylib.mm"
include "impbii.mm"

theorem oppggrpb
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let cI: class I
  assume oppgbas.1: |- O = ( oppG ` R )


  assert |- ( R e. Grp <-> O e. Grp )

  proof
    cR
    cgrp
    wcel
    #
    cO
    cgrp
    wcel
    #
    cR
    cO
    oppgbas.1
    oppggrp
    @1
    cO
    coppg
    cfv
    #
    cgrp
    wcel
    #
    @0
    cO
    @2
    @2
    eqid
    #
    oppggrp
    @3
    @0
    wb
    wtru
    vx
    vy
    cR
    cbs
    cfv
    #
    @2
    cR
    @5
    @2
    cbs
    cfv
    wceq
    wtru
    @5
    cO
    @2
    @4
    @5
    cR
    cO
    oppgbas.1
    @5
    eqid
    oppgbas
    oppgbas
    a1i
    wtru
    @5
    eqidd
    vx
    cv
    #
    vy
    cv
    #
    @2
    cplusg
    cfv
    #
    co
    #
    @6
    @7
    cR
    cplusg
    cfv
    #
    co
    #
    wceq
    wtru
    @6
    @5
    wcel
    @7
    @5
    wcel
    wa
    wa
    @9
    @7
    @6
    cO
    cplusg
    cfv
    #
    co
    @11
    @12
    @8
    cO
    @2
    @6
    @7
    @12
    eqid
    #
    @4
    @8
    eqid
    oppgplus
    @10
    @12
    cR
    cO
    @7
    @6
    @10
    eqid
    oppgbas.1
    @13
    oppgplus
    eqtri
    a1i
    grppropd
    trud
    sylib
    impbii
end
