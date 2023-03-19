include "cgrp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cgim.mm"
include "cplusg.mm"
include "eqid.mm"
include "oppgbas.mm"
include "id.mm"
include "oppggrp.mm"
include "grpinvf.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "grpinvadd.mm"
include "3expb.mm"
include "oppgplus.mm"
include "syl6eqr.mm"
include "isghmd.mm"
include "grpinvf1o.mm"
include "isgim.mm"
include "sylanbrc.mm"

theorem invoppggim
  let cG: class G
  let cI: class I
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume invoppggim.o: |- O = ( oppG ` G )
  assume invoppggim.i: |- I = ( invg ` G )


  assert |- ( G e. Grp -> I e. ( G GrpIso O ) )

  proof
    cG
    cgrp
    wcel
    #
    cI
    cG
    cO
    cghm
    co
    wcel
    cG
    cbs
    cfv
    #
    @1
    cI
    wf1o
    cI
    cG
    cO
    cgim
    co
    wcel
    @0
    vx
    vy
    cG
    cplusg
    cfv
    #
    cO
    cplusg
    cfv
    #
    cG
    cO
    cI
    @1
    @1
    @1
    eqid
    #
    @1
    cG
    cO
    invoppggim.o
    @4
    oppgbas
    #
    @2
    eqid
    #
    @3
    eqid
    #
    @0
    id
    #
    cG
    cO
    invoppggim.o
    oppggrp
    @1
    cG
    cI
    @4
    invoppggim.i
    grpinvf
    @0
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    wa
    @9
    @11
    @2
    co
    cI
    cfv
    #
    @11
    cI
    cfv
    #
    @9
    cI
    cfv
    #
    @2
    co
    #
    @15
    @14
    @3
    co
    @0
    @10
    @12
    @13
    @16
    wceq
    @1
    @2
    cG
    cI
    @9
    @11
    @4
    @6
    invoppggim.i
    grpinvadd
    3expb
    @2
    @3
    cG
    cO
    @15
    @14
    @6
    invoppggim.o
    @7
    oppgplus
    syl6eqr
    isghmd
    @0
    @1
    cG
    cI
    @4
    invoppggim.i
    @8
    grpinvf1o
    @1
    @1
    cG
    cO
    cI
    @4
    @5
    isgim
    sylanbrc
end
