include "wcel.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "hashcl.mm"
include "cr.mm"
include "nn0re.mm"
include "wn.mm"
include "wa.mm"
include "cpnf.mm"
include "pnfnre.mm"
include "neli.mm"
include "hashinf.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "ex.mm"
include "con4d.mm"
include "syl5.mm"
include "impbid2.mm"

theorem hashclb
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. Fin <-> ( # ` A ) e. NN0 ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    chash
    cfv
    #
    cn0
    wcel
    #
    cA
    hashcl
    @3
    @2
    cr
    wcel
    #
    @0
    @1
    @2
    nn0re
    @0
    @1
    @4
    @0
    @1
    wn
    #
    @4
    wn
    @0
    @5
    wa
    #
    @4
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    @6
    @2
    cpnf
    cr
    cA
    cV
    hashinf
    eleq1d
    mtbiri
    ex
    con4d
    syl5
    impbid2
end
