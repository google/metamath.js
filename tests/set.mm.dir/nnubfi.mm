include "cn.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cfn.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "fzfi.mm"
include "wi.mm"
include "wral.mm"
include "cn0.mm"
include "cle.mm"
include "ssel2.mm"
include "nnnn0.mm"
include "syl.mm"
include "adantlr.mm"
include "adantr.mm"
include "ad3antlr.mm"
include "cr.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "ltle.mm"
include "syl2anc.mm"
include "imp.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "ssfi.mm"
include "sylancr.mm"

theorem nnubfi
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ NN /\ B e. NN ) -> { x e. A | x < B } e. Fin )

  proof
    cA
    cn
    wss
    #
    cB
    cn
    wcel
    #
    wa
    #
    cc0
    cB
    cfz
    co
    #
    cfn
    wcel
    vx
    cv
    #
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    #
    @3
    wss
    #
    @6
    cfn
    wcel
    cc0
    cB
    fzfi
    @2
    @5
    @4
    @3
    wcel
    #
    wi
    #
    vx
    cA
    wral
    @7
    @2
    @9
    vx
    cA
    @2
    @4
    cA
    wcel
    #
    wa
    #
    @5
    @8
    @11
    @5
    wa
    @4
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    @4
    cB
    cle
    wbr
    #
    @8
    @11
    @12
    @5
    @0
    @10
    @12
    @1
    @0
    @10
    wa
    #
    @4
    cn
    wcel
    #
    @12
    cA
    cn
    @4
    ssel2
    #
    @4
    nnnn0
    syl
    adantlr
    adantr
    @1
    @13
    @0
    @10
    @5
    cB
    nnnn0
    ad3antlr
    @11
    @5
    @14
    @11
    @4
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @5
    @14
    wi
    @0
    @10
    @18
    @1
    @15
    @16
    @18
    @17
    @4
    nnre
    syl
    adantlr
    @1
    @19
    @0
    @10
    cB
    nnre
    ad2antlr
    @4
    cB
    ltle
    syl2anc
    imp
    @4
    cB
    elfz2nn0
    syl3anbrc
    ex
    ralrimiva
    @5
    vx
    cA
    @3
    rabss
    sylibr
    @3
    @6
    ssfi
    sylancr
end
