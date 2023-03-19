include "cgrp.mm"
include "wcel.mm"
include "cminusg.mm"
include "cfv.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "grpinvf.mm"
include "wa.mm"
include "oppgplus.mm"
include "grprinv.mm"
include "syl5eq.mm"
include "ralrimiva.mm"
include "wb.mm"
include "oppggrp.mm"
include "oppgbas.mm"
include "oppgid.mm"
include "isgrpinv.mm"
include "syl.mm"
include "mpbi2and.mm"
include "eqcomd.mm"

theorem oppginv
  let cR: class R
  let cI: class I
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  assume oppgbas.1: |- O = ( oppG ` R )
  assume oppginv.2: |- I = ( invg ` R )


  assert |- ( R e. Grp -> I = ( invg ` O ) )

  proof
    cR
    cgrp
    wcel
    #
    cO
    cminusg
    cfv
    #
    cI
    @0
    cR
    cbs
    cfv
    #
    @2
    cI
    wf
    #
    vx
    cv
    #
    cI
    cfv
    #
    @4
    cO
    cplusg
    cfv
    #
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vx
    @2
    wral
    #
    @1
    cI
    wceq
    #
    @2
    cR
    cI
    @2
    eqid
    #
    oppginv.2
    grpinvf
    @0
    @9
    vx
    @2
    @0
    @4
    @2
    wcel
    wa
    @7
    @4
    @5
    cR
    cplusg
    cfv
    #
    co
    @8
    @13
    @6
    cR
    cO
    @5
    @4
    @13
    eqid
    #
    oppgbas.1
    @6
    eqid
    #
    oppgplus
    @2
    @13
    cR
    cI
    @4
    @8
    @12
    @14
    @8
    eqid
    #
    oppginv.2
    grprinv
    syl5eq
    ralrimiva
    @0
    cO
    cgrp
    wcel
    @3
    @10
    wa
    @11
    wb
    cR
    cO
    oppgbas.1
    oppggrp
    vx
    @2
    @6
    cO
    cI
    @1
    @8
    @2
    cR
    cO
    oppgbas.1
    @12
    oppgbas
    @15
    cR
    cO
    @8
    oppgbas.1
    @16
    oppgid
    @1
    eqid
    isgrpinv
    syl
    mpbi2and
    eqcomd
end
