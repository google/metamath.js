include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "cpfx.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "3simpa.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "oveq2i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "swrdccatin1.mm"
include "sylc.mm"
include "ccatcl.mm"
include "3adant3.mm"
include "pfxval.mm"
include "sylan2.mm"
include "3adant2.mm"
include "3eqtr4d.mm"

theorem pfxccatpfx1
  let cA: class A
  let cB: class B
  let cL: class L
  let cN: class N
  let cV: class V
  let vk: setvar k
  let cM: class M
  let vx: setvar x
  assume pfxccatin12.l: |- L = ( # ` A )


  assert |- ( ( A e. Word V /\ B e. Word V /\ N e. ( 0 ... L ) ) -> ( ( A ++ B ) prefix N ) = ( A prefix N ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cN
    cc0
    cL
    cfz
    co
    #
    wcel
    #
    w3a
    #
    cA
    cB
    cconcat
    co
    #
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    cA
    @7
    csubstr
    co
    #
    @6
    cN
    cpfx
    co
    #
    cA
    cN
    cpfx
    co
    #
    @5
    @1
    @2
    wa
    cc0
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    cA
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @8
    @9
    wceq
    @1
    @2
    @4
    3simpa
    @4
    @1
    @16
    @2
    @4
    @12
    @15
    @4
    cN
    cn0
    wcel
    #
    @12
    cN
    cL
    elfznn0
    #
    cN
    0elfz
    syl
    @4
    @15
    @3
    @14
    cN
    cL
    @13
    cc0
    cfz
    pfxccatin12.l
    oveq2i
    eleq2i
    biimpi
    jca
    3ad2ant3
    cA
    cB
    cc0
    cN
    cV
    swrdccatin1
    sylc
    @5
    @6
    @0
    wcel
    #
    @17
    wa
    @10
    @8
    wceq
    @5
    @19
    @17
    @1
    @2
    @19
    @4
    cV
    cA
    cB
    ccatcl
    3adant3
    @4
    @1
    @17
    @2
    @18
    3ad2ant3
    jca
    @6
    cN
    @0
    pfxval
    syl
    @1
    @4
    @11
    @9
    wceq
    #
    @2
    @4
    @1
    @17
    @20
    @18
    cA
    cN
    @0
    pfxval
    sylan2
    3adant2
    3eqtr4d
end
