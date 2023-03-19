include "ccat.mm"
include "wcel.mm"
include "cv.mm"
include "ciso.mm"
include "cfv.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "ccic.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-cic.mm"
include "a1i.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "adantl.mm"
include "id.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem cicfval
  let cC: class C
  let vc: setvar c


  assert |- ( C e. Cat -> ( ~=c ` C ) = ( ( Iso ` C ) supp (/) ) )

  proof
    cC
    ccat
    wcel
    #
    vc
    cC
    vc
    cv
    #
    ciso
    cfv
    #
    c0
    csupp
    co
    #
    cC
    ciso
    cfv
    #
    c0
    csupp
    co
    #
    ccat
    ccic
    cvv
    ccic
    vc
    ccat
    @3
    cmpt
    wceq
    @0
    vc
    df-cic
    a1i
    @1
    cC
    wceq
    #
    @3
    @5
    wceq
    @0
    @6
    @2
    @4
    c0
    csupp
    @1
    cC
    ciso
    fveq2
    oveq1d
    adantl
    @0
    id
    @0
    @4
    c0
    csupp
    ovexd
    fvmptd
end
