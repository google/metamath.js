include "c0.mm"
include "cpr.mm"
include "c1.mm"
include "cop.mm"
include "c9.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cts.mm"
include "basendx.mm"
include "opeq1i.mm"
include "tsetndx.mm"
include "preq12i.mm"
include "eqtr4i.mm"
include "cvv.mm"
include "wcel.mm"
include "ctopon.mm"
include "indistopon.mm"
include "ax-mp.mm"
include "toponunii.mm"
include "indistop.mm"
include "eltpsi.mm"

theorem indistpsx
  let cA: class A
  let cK: class K
  assume indistpsx.a: |- A e. _V
  assume indistpsx.k: |- K = { <. 1 , A >. , <. 9 , { (/) , A } >. }


  assert |- K e. TopSp

  proof
    cA
    c0
    cA
    cpr
    #
    cK
    cK
    c1
    cA
    cop
    #
    c9
    @0
    cop
    #
    cpr
    cnx
    cbs
    cfv
    #
    cA
    cop
    #
    cnx
    cts
    cfv
    #
    @0
    cop
    #
    cpr
    indistpsx.k
    @4
    @1
    @6
    @2
    @3
    c1
    cA
    basendx
    opeq1i
    @5
    c9
    @0
    tsetndx
    opeq1i
    preq12i
    eqtr4i
    cA
    @0
    cA
    cvv
    wcel
    @0
    cA
    ctopon
    cfv
    wcel
    indistpsx.a
    cA
    cvv
    indistopon
    ax-mp
    toponunii
    cA
    indistop
    eltpsi
end
