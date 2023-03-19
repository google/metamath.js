include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "cz.mm"
include "wn.mm"
include "nn0z.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antrr.mm"
include "recnd.mm"
include "sqsqrtd.mm"
include "breqtrrd.mm"
include "cc0.mm"
include "cle.mm"
include "nn0ge0.mm"
include "resqrtcld.mm"
include "sqrtge0d.mm"
include "lt2sqd.mm"
include "mpbird.mm"
include "simprr.mm"
include "eqbrtrd.mm"
include "peano2re.mm"
include "syl.mm"
include "peano2nn0.mm"
include "btwnnz.mm"
include "syl3anc.mm"
include "wi.mm"
include "zsqrtelqelz.mm"
include "ex.mm"
include "mtod.mm"

theorem nonsq
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vx: setvar x


  assert |- ( ( ( A e. NN0 /\ B e. NN0 ) /\ ( ( B ^ 2 ) < A /\ A < ( ( B + 1 ) ^ 2 ) ) ) -> -. ( sqrt ` A ) e. QQ )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cB
    c2
    cexp
    co
    #
    cA
    clt
    wbr
    #
    cA
    cB
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    csqrt
    cfv
    #
    cq
    wcel
    #
    @10
    cz
    wcel
    #
    @9
    cB
    cz
    wcel
    #
    cB
    @10
    clt
    wbr
    #
    @10
    @5
    clt
    wbr
    #
    @12
    wn
    @1
    @13
    @0
    @8
    cB
    nn0z
    ad2antlr
    @9
    @14
    @3
    @10
    c2
    cexp
    co
    #
    clt
    wbr
    @9
    @3
    cA
    @16
    clt
    @2
    @4
    @7
    simprl
    @9
    cA
    @9
    cA
    @0
    cA
    cr
    wcel
    @1
    @8
    cA
    nn0re
    ad2antrr
    #
    recnd
    sqsqrtd
    #
    breqtrrd
    @9
    cB
    @10
    @1
    cB
    cr
    wcel
    #
    @0
    @8
    cB
    nn0re
    ad2antlr
    #
    @9
    cA
    @17
    @0
    cc0
    cA
    cle
    wbr
    @1
    @8
    cA
    nn0ge0
    ad2antrr
    #
    resqrtcld
    #
    @1
    cc0
    cB
    cle
    wbr
    @0
    @8
    cB
    nn0ge0
    ad2antlr
    @9
    cA
    @17
    @21
    sqrtge0d
    #
    lt2sqd
    mpbird
    @9
    @15
    @16
    @6
    clt
    wbr
    @9
    @16
    cA
    @6
    clt
    @18
    @2
    @4
    @7
    simprr
    eqbrtrd
    @9
    @10
    @5
    @22
    @9
    @19
    @5
    cr
    wcel
    @20
    cB
    peano2re
    syl
    @23
    @1
    cc0
    @5
    cle
    wbr
    #
    @0
    @8
    @1
    @5
    cn0
    wcel
    @24
    cB
    peano2nn0
    @5
    nn0ge0
    syl
    ad2antlr
    lt2sqd
    mpbird
    cB
    @10
    btwnnz
    syl3anc
    @9
    cA
    cz
    wcel
    #
    @11
    @12
    wi
    @0
    @25
    @1
    @8
    cA
    nn0z
    ad2antrr
    @25
    @11
    @12
    cA
    zsqrtelqelz
    ex
    syl
    mtod
end
