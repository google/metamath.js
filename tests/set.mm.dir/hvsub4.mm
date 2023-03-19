include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "cmv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "wceq.mm"
include "hvaddcl.mm"
include "hvsubval.mm"
include "syl2an.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "oveq12d.mm"
include "cc.mm"
include "neg1cn.mm"
include "ax-hvdistr1.mm"
include "mp3an1.mm"
include "adantl.mm"
include "oveq2d.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "anim2i.mm"
include "anim12i.mm"
include "an4s.mm"
include "hvadd4.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem hvsub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( A +h B ) -h ( C +h D ) ) = ( ( A -h C ) +h ( B -h D ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cva
    co
    #
    cC
    cD
    cva
    co
    #
    cmv
    co
    #
    @7
    c1
    cneg
    #
    @8
    csm
    co
    #
    cva
    co
    #
    cA
    cC
    cmv
    co
    #
    cB
    cD
    cmv
    co
    #
    cva
    co
    #
    @2
    @7
    chil
    wcel
    @8
    chil
    wcel
    @9
    @12
    wceq
    @5
    cA
    cB
    hvaddcl
    cC
    cD
    hvaddcl
    @7
    @8
    hvsubval
    syl2an
    @6
    @15
    cA
    @10
    cC
    csm
    co
    #
    cva
    co
    #
    cB
    @10
    cD
    csm
    co
    #
    cva
    co
    #
    cva
    co
    #
    @12
    @6
    @13
    @17
    @14
    @19
    cva
    @0
    @3
    @13
    @17
    wceq
    @1
    @4
    cA
    cC
    hvsubval
    ad2ant2r
    @1
    @4
    @14
    @19
    wceq
    @0
    @3
    cB
    cD
    hvsubval
    ad2ant2l
    oveq12d
    @6
    @12
    @7
    @16
    @18
    cva
    co
    #
    cva
    co
    #
    @20
    @6
    @11
    @21
    @7
    cva
    @5
    @11
    @21
    wceq
    #
    @2
    @10
    cc
    wcel
    #
    @3
    @4
    @23
    neg1cn
    @10
    cC
    cD
    ax-hvdistr1
    mp3an1
    adantl
    oveq2d
    @6
    @0
    @16
    chil
    wcel
    #
    wa
    #
    @1
    @18
    chil
    wcel
    #
    wa
    #
    wa
    #
    @20
    @22
    wceq
    @0
    @3
    @1
    @4
    @29
    @0
    @3
    wa
    @26
    @1
    @4
    wa
    @28
    @3
    @25
    @0
    @24
    @3
    @25
    neg1cn
    @10
    cC
    hvmulcl
    mpan
    anim2i
    @4
    @27
    @1
    @24
    @4
    @27
    neg1cn
    @10
    cD
    hvmulcl
    mpan
    anim2i
    anim12i
    an4s
    cA
    @16
    cB
    @18
    hvadd4
    syl
    eqtr4d
    eqtr4d
    eqtr4d
end
