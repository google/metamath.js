include "cgrp.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cv.mm"
include "cminusg.mm"
include "c0g.mm"
include "wceq.mm"
include "eqid.mm"
include "oppgbas.mm"
include "a1i.mm"
include "eqidd.mm"
include "oppgid.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "oppgmnd.mm"
include "syl.mm"
include "grpinvcl.mm"
include "wa.mm"
include "co.mm"
include "oppgplus.mm"
include "grprinv.mm"
include "syl5eq.mm"
include "isgrpd2.mm"

theorem oppggrp
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let cI: class I
  assume oppgbas.1: |- O = ( oppG ` R )


  assert |- ( R e. Grp -> O e. Grp )

  proof
    cR
    cgrp
    wcel
    #
    vx
    cR
    cbs
    cfv
    #
    cO
    cplusg
    cfv
    #
    cO
    vx
    cv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    @1
    cO
    cbs
    cfv
    wceq
    @0
    @1
    cR
    cO
    oppgbas.1
    @1
    eqid
    #
    oppgbas
    a1i
    @0
    @2
    eqidd
    @6
    cO
    c0g
    cfv
    wceq
    @0
    cR
    cO
    @6
    oppgbas.1
    @6
    eqid
    #
    oppgid
    a1i
    @0
    cR
    cmnd
    wcel
    cO
    cmnd
    wcel
    cR
    grpmnd
    cR
    cO
    oppgbas.1
    oppgmnd
    syl
    @1
    cR
    @4
    @3
    @7
    @4
    eqid
    #
    grpinvcl
    @0
    @3
    @1
    wcel
    wa
    @5
    @3
    @2
    co
    @3
    @5
    cR
    cplusg
    cfv
    #
    co
    @6
    @10
    @2
    cR
    cO
    @5
    @3
    @10
    eqid
    #
    oppgbas.1
    @2
    eqid
    oppgplus
    @1
    @10
    cR
    @4
    @3
    @6
    @7
    @11
    @8
    @9
    grprinv
    syl5eq
    isgrpd2
end
