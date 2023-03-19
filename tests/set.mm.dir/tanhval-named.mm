include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ctan.mm"
include "cfv.mm"
include "cdiv.mm"
include "ccosh.mm"
include "ccnv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "ctanh.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "df-tanh.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem tanhval-named
  let cA: class A
  let vx: setvar x
  let vk: setvar k


  assert |- ( A e. ( `' cosh " ( CC \ { 0 } ) ) -> ( tanh ` A ) = ( ( tan ` ( _i x. A ) ) / _i ) )

  proof
    vx
    cA
    ci
    vx
    cv
    #
    cmul
    co
    #
    ctan
    cfv
    #
    ci
    cdiv
    co
    ci
    cA
    cmul
    co
    #
    ctan
    cfv
    #
    ci
    cdiv
    co
    ccosh
    ccnv
    cc
    cc0
    csn
    cdif
    cima
    ctanh
    @0
    cA
    wceq
    #
    @2
    @4
    ci
    cdiv
    @5
    @1
    @3
    ctan
    @0
    cA
    ci
    cmul
    oveq2
    fveq2d
    oveq1d
    vx
    df-tanh
    @4
    ci
    cdiv
    ovex
    fvmpt
end
