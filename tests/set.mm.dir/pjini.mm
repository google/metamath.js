include "cin.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "cch.mm"
include "wceq.mm"
include "inss1.mm"
include "sseli.mm"
include "pjid.mm"
include "sylancr.mm"
include "eleq1d.mm"
include "ibir.mm"

theorem pjini
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjocin.1: |- G e. CH
  assume pjocin.2: |- H e. CH


  assert |- ( A e. ( G i^i H ) -> ( ( projh ` G ) ` A ) e. ( G i^i H ) )

  proof
    cA
    cG
    cH
    cin
    #
    wcel
    #
    cA
    cG
    cpjh
    cfv
    cfv
    #
    @0
    wcel
    @1
    @2
    cA
    @0
    @1
    cG
    cch
    wcel
    cA
    cG
    wcel
    @2
    cA
    wceq
    pjocin.1
    @0
    cG
    cA
    cG
    cH
    inss1
    sseli
    cA
    cG
    pjid
    sylancr
    eleq1d
    ibir
end
