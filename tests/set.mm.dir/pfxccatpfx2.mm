include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "w3a.mm"
include "cconcat.mm"
include "cpfx.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cmin.mm"
include "cn0.mm"
include "wceq.mm"
include "ccatcl.mm"
include "3adant3.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "chash.mm"
include "lencl.mm"
include "syl5eqel.mm"
include "elfzuz.mm"
include "peano2nn0.mm"
include "anim1i.mm"
include "syl2an.mm"
include "3adant2.mm"
include "eluznn0.mm"
include "syl.mm"
include "pfxval.mm"
include "syl2anc.mm"
include "3simpa.mm"
include "3ad2ant1.mm"
include "0elfz.mm"
include "wss.mm"
include "cz.mm"
include "nn0zd.mm"
include "adantr.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzss1.mm"
include "3syl.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "syl6sseqr.mm"
include "sseld.mm"
include "3impia.mm"
include "jca.mm"
include "pfxccatin12.mm"
include "sylc.mm"
include "opeq2i.mm"
include "swrdid.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem pfxccatpfx2
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume pfxccatin12.l: |- L = ( # ` A )
  assume pfxccatpfx2.m: |- M = ( # ` B )


  assert |- ( ( A e. Word V /\ B e. Word V /\ N e. ( ( L + 1 ) ... ( L + M ) ) ) -> ( ( A ++ B ) prefix N ) = ( A ++ ( B prefix ( N - L ) ) ) )

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
    cL
    c1
    caddc
    co
    #
    cL
    cM
    caddc
    co
    #
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
    cN
    cpfx
    co
    #
    @8
    cc0
    cN
    cop
    csubstr
    co
    #
    cA
    cc0
    cL
    cop
    #
    csubstr
    co
    #
    cB
    cN
    cL
    cmin
    co
    cpfx
    co
    #
    cconcat
    co
    #
    cA
    @13
    cconcat
    co
    @7
    @8
    @0
    wcel
    #
    cN
    cn0
    wcel
    #
    @9
    @10
    wceq
    @1
    @2
    @15
    @6
    cV
    cA
    cB
    ccatcl
    3adant3
    @7
    @3
    cn0
    wcel
    #
    cN
    @3
    cuz
    cfv
    wcel
    #
    wa
    #
    @16
    @1
    @6
    @19
    @2
    @1
    cL
    cn0
    wcel
    #
    @18
    @19
    @6
    @1
    cL
    cA
    chash
    cfv
    #
    cn0
    pfxccatin12.l
    cV
    cA
    lencl
    #
    syl5eqel
    #
    cN
    @3
    @4
    elfzuz
    @20
    @17
    @18
    cL
    peano2nn0
    anim1i
    syl2an
    3adant2
    cN
    @3
    eluznn0
    syl
    @8
    cN
    @0
    pfxval
    syl2anc
    @7
    @1
    @2
    wa
    #
    cc0
    cc0
    cL
    cfz
    co
    wcel
    #
    cN
    cL
    cL
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    @10
    @14
    wceq
    @1
    @2
    @6
    3simpa
    @7
    @25
    @29
    @7
    @20
    @25
    @1
    @2
    @20
    @6
    @23
    3ad2ant1
    cL
    0elfz
    syl
    @1
    @2
    @6
    @29
    @24
    @5
    @28
    cN
    @24
    @5
    cL
    @4
    cfz
    co
    #
    @28
    @24
    cL
    cL
    cuz
    cfv
    #
    wcel
    #
    @3
    @31
    wcel
    @5
    @30
    wss
    @24
    cL
    cz
    wcel
    #
    @32
    @1
    @33
    @2
    @1
    cL
    @21
    cz
    pfxccatin12.l
    @1
    @21
    @22
    nn0zd
    syl5eqel
    adantr
    cL
    uzid
    syl
    cL
    cL
    peano2uz
    @3
    cL
    @4
    fzss1
    3syl
    @27
    @4
    cL
    cfz
    @26
    cM
    cL
    caddc
    cM
    @26
    pfxccatpfx2.m
    eqcomi
    oveq2i
    oveq2i
    syl6sseqr
    sseld
    3impia
    jca
    cA
    cB
    cL
    cc0
    cN
    cV
    pfxccatin12.l
    pfxccatin12
    sylc
    @7
    @12
    cA
    @13
    cconcat
    @1
    @2
    @12
    cA
    wceq
    @6
    @1
    @12
    cA
    cc0
    @21
    cop
    #
    csubstr
    co
    cA
    @11
    @34
    cA
    csubstr
    cL
    @21
    cc0
    pfxccatin12.l
    opeq2i
    oveq2i
    cV
    cA
    swrdid
    syl5eq
    3ad2ant1
    oveq1d
    3eqtrd
end
