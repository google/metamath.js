include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "cint.mm"
include "cdm.mm"
include "cvv.mm"
include "cxp.mm"
include "wceq.mm"
include "wss.mm"
include "df-rel.mm"
include "biimpi.mm"
include "sselda.mm"
include "1stval2.mm"
include "syl.mm"
include "elreldm.mm"
include "eqeltrd.mm"

theorem 1stdm
  let cA: class A
  let cR: class R


  assert |- ( ( Rel R /\ A e. R ) -> ( 1st ` A ) e. dom R )

  proof
    cR
    wrel
    #
    cA
    cR
    wcel
    wa
    #
    cA
    c1st
    cfv
    #
    cA
    cint
    cint
    #
    cR
    cdm
    @1
    cA
    cvv
    cvv
    cxp
    #
    wcel
    @2
    @3
    wceq
    @0
    cR
    @4
    cA
    @0
    cR
    @4
    wss
    cR
    df-rel
    biimpi
    sselda
    cA
    1stval2
    syl
    cR
    cA
    elreldm
    eqeltrd
end
