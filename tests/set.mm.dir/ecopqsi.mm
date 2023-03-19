include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "cec.mm"
include "opelxpi.mm"
include "cqs.mm"
include "ecelqsi.mm"
include "syl6eleqr.mm"
include "syl.mm"

theorem ecopqsi
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume ecopqsi.1: |- R e. _V
  assume ecopqsi.2: |- S = ( ( A X. A ) /. R )


  assert |- ( ( B e. A /\ C e. A ) -> [ <. B , C >. ] R e. S )

  proof
    cB
    cA
    wcel
    cC
    cA
    wcel
    wa
    cB
    cC
    cop
    #
    cA
    cA
    cxp
    #
    wcel
    #
    @0
    cR
    cec
    #
    cS
    wcel
    cB
    cC
    cA
    cA
    opelxpi
    @2
    @3
    @1
    cR
    cqs
    cS
    @1
    @0
    cR
    ecopqsi.1
    ecelqsi
    ecopqsi.2
    syl6eleqr
    syl
end
