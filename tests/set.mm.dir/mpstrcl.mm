include "cotp.mm"
include "wcel.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "w3a.mm"
include "df-ot.mm"
include "mpstssv.mm"
include "sseli.mm"
include "syl5eqelr.mm"
include "wa.mm"
include "opelxp.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "sylib.mm"

theorem mpstrcl
  let cA: class A
  let cD: class D
  let cP: class P
  let cT: class T
  let cH: class H
  let va: setvar a
  let vh: setvar h
  let vs: setvar s
  let vz: setvar z
  let cR: class R
  let vd: setvar d
  assume mpstssv.p: |- P = ( mPreSt ` T )


  assert |- ( <. D , H , A >. e. P -> ( D e. _V /\ H e. _V /\ A e. _V ) )

  proof
    cD
    cH
    cA
    cotp
    #
    cP
    wcel
    #
    cD
    cH
    cop
    #
    cA
    cop
    #
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    wcel
    #
    cD
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    w3a
    #
    @1
    @3
    @0
    @5
    cD
    cH
    cA
    df-ot
    cP
    @5
    @0
    cP
    cT
    mpstssv.p
    mpstssv
    sseli
    syl5eqelr
    @2
    @4
    wcel
    #
    @9
    wa
    @7
    @8
    wa
    #
    @9
    wa
    @6
    @10
    @11
    @12
    @9
    cD
    cH
    cvv
    cvv
    opelxp
    anbi1i
    @2
    cA
    @4
    cvv
    opelxp
    @7
    @8
    @9
    df-3an
    3bitr4i
    sylib
end
