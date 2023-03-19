include "wiso.mm"
include "wor.mm"
include "ccnv.mm"
include "wi.mm"
include "isocnv.mm"
include "isosolem.mm"
include "syl.mm"
include "impbid.mm"

theorem isoso
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f


  assert |- ( H Isom R , S ( A , B ) -> ( R Or A <-> S Or B ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cA
    cR
    wor
    #
    cB
    cS
    wor
    #
    @0
    cB
    cA
    cS
    cR
    cH
    ccnv
    #
    wiso
    @1
    @2
    wi
    cA
    cB
    cR
    cS
    cH
    isocnv
    cB
    cA
    cS
    cR
    @3
    isosolem
    syl
    cA
    cB
    cR
    cS
    cH
    isosolem
    impbid
end
