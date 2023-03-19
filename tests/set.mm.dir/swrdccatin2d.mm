include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cconcat.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "cmin.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "caddc.mm"
include "adantl.mm"
include "jca.mm"
include "wb.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "eqid.mm"
include "swrdccatin2.mm"
include "imp.mm"
include "syl6.mm"
include "oveq2.mm"
include "opeq12d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "sylibd.mm"
include "mpcom.mm"

theorem swrdccatin2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  assume swrdccatind.l: |- ( ph -> ( # ` A ) = L )
  assume swrdccatind.w: |- ( ph -> ( A e. Word V /\ B e. Word V ) )
  assume swrdccatin2d.1: |- ( ph -> M e. ( L ... N ) )
  assume swrdccatin2d.2: |- ( ph -> N e. ( L ... ( L + ( # ` B ) ) ) )


  assert |- ( ph -> ( ( A ++ B ) substr <. M , N >. ) = ( B substr <. ( M - L ) , ( N - L ) >. ) )

  proof
    cA
    chash
    cfv
    #
    cL
    wceq
    #
    wph
    cA
    cB
    cconcat
    co
    cM
    cN
    cop
    csubstr
    co
    #
    cB
    cM
    cL
    cmin
    co
    #
    cN
    cL
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    wceq
    #
    swrdccatind.l
    @1
    wph
    @2
    cB
    cM
    @0
    cmin
    co
    #
    cN
    @0
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    wceq
    #
    @7
    @1
    wph
    cA
    cV
    cword
    #
    wcel
    cB
    @13
    wcel
    wa
    #
    cM
    @0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    @0
    @0
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
    #
    wa
    #
    @12
    @1
    wph
    @22
    @1
    wph
    wa
    #
    @14
    @21
    wph
    @14
    @1
    swrdccatind.w
    adantl
    @23
    @21
    cM
    cL
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cL
    cL
    @17
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    wph
    @29
    @1
    wph
    @25
    @28
    swrdccatin2d.1
    swrdccatin2d.2
    jca
    adantl
    @1
    @21
    @29
    wb
    wph
    @1
    @16
    @25
    @20
    @28
    @1
    @15
    @24
    cM
    @0
    cL
    cN
    cfz
    oveq1
    eleq2d
    @1
    @19
    @27
    cN
    @1
    @0
    cL
    @18
    @26
    cfz
    @1
    id
    @0
    cL
    @17
    caddc
    oveq1
    oveq12d
    eleq2d
    anbi12d
    adantr
    mpbird
    jca
    ex
    @14
    @21
    @12
    cA
    cB
    @0
    cM
    cN
    cV
    @0
    eqid
    swrdccatin2
    imp
    syl6
    @1
    @11
    @6
    @2
    @1
    @10
    @5
    cB
    csubstr
    @1
    @8
    @3
    @9
    @4
    @0
    cL
    cM
    cmin
    oveq2
    @0
    cL
    cN
    cmin
    oveq2
    opeq12d
    oveq2d
    eqeq2d
    sylibd
    mpcom
end
