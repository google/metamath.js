include "cv.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "wcel.mm"
include "cxme.mm"
include "cmt.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "df-ms.mm"
include "elrab2.mm"

theorem isms
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume isms.j: |- J = ( TopOpen ` K )
  assume isms.x: |- X = ( Base ` K )
  assume isms.d: |- D = ( ( dist ` K ) |` ( X X. X ) )


  assert |- ( K e. MetSp <-> ( K e. *MetSp /\ D e. ( Met ` X ) ) )

  proof
    vf
    cv
    #
    cds
    cfv
    #
    @0
    cbs
    cfv
    #
    @2
    cxp
    #
    cres
    #
    @2
    cme
    cfv
    #
    wcel
    cD
    cX
    cme
    cfv
    #
    wcel
    vf
    cK
    cxme
    cmt
    @0
    cK
    wceq
    #
    @4
    cD
    @5
    @6
    @7
    @4
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
    @7
    @1
    @8
    @3
    @9
    @0
    cK
    cds
    fveq2
    @7
    @2
    cX
    @7
    @2
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
    #
    sqxpeqd
    reseq12d
    isms.d
    syl6eqr
    @7
    @2
    cX
    cme
    @10
    fveq2d
    eleq12d
    vf
    df-ms
    elrab2
end
