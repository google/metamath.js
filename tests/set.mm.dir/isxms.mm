include "cv.mm"
include "ctopn.mm"
include "cfv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wceq.mm"
include "ctps.mm"
include "cxme.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "df-xms.mm"
include "elrab2.mm"

theorem isxms
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume isms.j: |- J = ( TopOpen ` K )
  assume isms.x: |- X = ( Base ` K )
  assume isms.d: |- D = ( ( dist ` K ) |` ( X X. X ) )


  assert |- ( K e. *MetSp <-> ( K e. TopSp /\ J = ( MetOpen ` D ) ) )

  proof
    vf
    cv
    #
    ctopn
    cfv
    #
    @0
    cds
    cfv
    #
    @0
    cbs
    cfv
    #
    @3
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    wceq
    cJ
    cD
    cmopn
    cfv
    #
    wceq
    vf
    cK
    ctps
    cxme
    @0
    cK
    wceq
    #
    @1
    cJ
    @6
    @7
    @8
    @1
    cK
    ctopn
    cfv
    cJ
    @0
    cK
    ctopn
    fveq2
    isms.j
    syl6eqr
    @8
    @5
    cD
    cmopn
    @8
    @5
    cK
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    cD
    @8
    @2
    @9
    @4
    @10
    @0
    cK
    cds
    fveq2
    @8
    @3
    cX
    @8
    @3
    cK
    cbs
    cfv
    cX
    @0
    cK
    cbs
    fveq2
    isms.x
    syl6eqr
    sqxpeqd
    reseq12d
    isms.d
    syl6eqr
    fveq2d
    eqeq12d
    vf
    df-xms
    elrab2
end
