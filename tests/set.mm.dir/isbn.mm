include "cnvc.mm"
include "ccms.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cbn.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "df-bn.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem isbn
  let cF: class F
  let cW: class W
  let vw: setvar w
  assume isbn.1: |- F = ( Scalar ` W )


  assert |- ( W e. Ban <-> ( W e. NrmVec /\ W e. CMetSp /\ F e. CMetSp ) )

  proof
    cW
    cnvc
    ccms
    cin
    #
    wcel
    #
    cF
    ccms
    wcel
    #
    wa
    cW
    cnvc
    wcel
    #
    cW
    ccms
    wcel
    #
    wa
    #
    @2
    wa
    cW
    cbn
    wcel
    @3
    @4
    @2
    w3a
    @1
    @5
    @2
    cW
    cnvc
    ccms
    elin
    anbi1i
    vw
    cv
    #
    csca
    cfv
    #
    ccms
    wcel
    @2
    vw
    cW
    @0
    cbn
    @6
    cW
    wceq
    #
    @7
    cF
    ccms
    @8
    @7
    cW
    csca
    cfv
    cF
    @6
    cW
    csca
    fveq2
    isbn.1
    syl6eqr
    eleq1d
    vw
    df-bn
    elrab2
    @3
    @4
    @2
    df-3an
    3bitr4i
end
