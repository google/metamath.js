include "cfcls.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "ctopon.mm"
include "cfv.mm"
include "cfil.mm"
include "wb.mm"
include "fclsfil.mm"
include "fclstopon.mm"
include "mpbird.mm"
include "fclsopn.mm"
include "syl2anc.mm"
include "ibi.mm"
include "simpld.mm"

theorem fclselbas
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vs: setvar s
  let cU: class U
  let cS: class S
  assume fclselbas.1: |- X = U. J


  assert |- ( A e. ( J fClus F ) -> A e. X )

  proof
    cA
    cJ
    cF
    cfcls
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    vo
    cv
    #
    wcel
    @2
    vs
    cv
    cin
    c0
    wne
    vs
    cF
    wral
    wi
    vo
    cJ
    wral
    #
    @0
    @1
    @3
    wa
    #
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    wcel
    #
    @0
    @4
    wb
    @0
    @5
    @6
    cA
    cF
    cJ
    cX
    fclselbas.1
    fclsfil
    #
    cA
    cF
    cJ
    cX
    fclstopon
    mpbird
    @7
    cA
    vo
    cF
    cJ
    cX
    vs
    fclsopn
    syl2anc
    ibi
    simpld
end
