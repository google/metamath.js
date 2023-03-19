include "wcel.mm"
include "wa.mm"
include "csg.mm"
include "cfv.mm"
include "ccom.mm"
include "cmopn.mm"
include "cnx.mm"
include "cds.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cts.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "fvex.mm"
include "tsetid.mm"
include "setsid.mm"
include "mp2an.mm"
include "eqid.mm"
include "tngds.mm"
include "syl6reqr.mm"
include "adantl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "tngval.mm"
include "3eqtr4a.mm"

theorem tngtset
  let cD: class D
  let cT: class T
  let cG: class G
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngtset.2: |- D = ( dist ` T )
  assume tngtset.3: |- J = ( MetOpen ` D )


  assert |- ( ( G e. V /\ N e. W ) -> J = ( TopSet ` T ) )

  proof
    cG
    cV
    wcel
    #
    cN
    cW
    wcel
    #
    wa
    #
    cN
    cG
    csg
    cfv
    #
    ccom
    #
    cmopn
    cfv
    #
    cG
    cnx
    cds
    cfv
    @4
    cop
    #
    csts
    co
    #
    cnx
    cts
    cfv
    @5
    cop
    csts
    co
    #
    cts
    cfv
    #
    cJ
    cT
    cts
    cfv
    @7
    cvv
    wcel
    @5
    cvv
    wcel
    @5
    @9
    wceq
    cG
    @6
    csts
    ovex
    @4
    cmopn
    fvex
    cvv
    @5
    cts
    cvv
    @7
    tsetid
    setsid
    mp2an
    @2
    cJ
    cD
    cmopn
    cfv
    @5
    tngtset.3
    @2
    cD
    @4
    cmopn
    @1
    cD
    @4
    wceq
    @0
    @1
    @4
    cT
    cds
    cfv
    cD
    cT
    cG
    @3
    cN
    cW
    tngbas.t
    @3
    eqid
    #
    tngds
    tngtset.2
    syl6reqr
    adantl
    fveq2d
    syl5eq
    @2
    cT
    @8
    cts
    @4
    cT
    cG
    @5
    @3
    cN
    cV
    cW
    tngbas.t
    @10
    @4
    eqid
    @5
    eqid
    tngval
    fveq2d
    3eqtr4a
end
