include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "crmy.mm"
include "co.mm"
include "cz.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nn0z.mm"
include "frmy.mm"
include "fovcl.mm"
include "sylan2.mm"
include "crmx.mm"
include "clt.mm"
include "rmxypos.mm"
include "simprd.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem rmynn0
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY N ) e. NN0 )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cN
    crmy
    co
    #
    cz
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    cn0
    wcel
    @2
    @1
    cN
    cz
    wcel
    @5
    cN
    nn0z
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    @3
    cc0
    cA
    cN
    crmx
    co
    clt
    wbr
    @6
    cA
    cN
    rmxypos
    simprd
    @4
    elnn0z
    sylanbrc
end
