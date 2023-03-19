include "cv.mm"
include "cds.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "cms.mm"
include "wcel.mm"
include "cbs.mm"
include "wsbc.mm"
include "cmt.mm"
include "ccms.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "fveq2.mm"
include "adantr.mm"
include "id.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "sbcied.mm"
include "df-cms.mm"
include "elrab2.mm"

theorem iscms
  let cD: class D
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vw: setvar w
  assume iscms.1: |- X = ( Base ` M )
  assume iscms.2: |- D = ( ( dist ` M ) |` ( X X. X ) )


  assert |- ( M e. CMetSp <-> ( M e. MetSp /\ D e. ( CMet ` X ) ) )

  proof
    vw
    cv
    #
    cds
    cfv
    #
    vb
    cv
    #
    @2
    cxp
    #
    cres
    #
    @2
    cms
    cfv
    #
    wcel
    #
    vb
    @0
    cbs
    cfv
    #
    wsbc
    cD
    cX
    cms
    cfv
    #
    wcel
    #
    vw
    cM
    cmt
    ccms
    @0
    cM
    wceq
    #
    @6
    @9
    vb
    @7
    cvv
    @10
    @0
    cbs
    fvexd
    @10
    @2
    @7
    wceq
    #
    wa
    #
    @4
    cD
    @5
    @8
    @12
    @4
    cM
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    cD
    @12
    @1
    @13
    @3
    @14
    @10
    @1
    @13
    wceq
    @11
    @0
    cM
    cds
    fveq2
    adantr
    @12
    @2
    cX
    @11
    @10
    @2
    @7
    cX
    @11
    id
    @10
    @7
    cM
    cbs
    cfv
    cX
    @0
    cM
    cbs
    fveq2
    iscms.1
    syl6eqr
    sylan9eqr
    #
    sqxpeqd
    reseq12d
    iscms.2
    syl6eqr
    @12
    @2
    cX
    cms
    @15
    fveq2d
    eleq12d
    sbcied
    vw
    vb
    df-cms
    elrab2
end
