include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cconcat.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "cc0.mm"
include "cmin.mm"
include "wa.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "caddc.mm"
include "adantl.mm"
include "jca.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "eqid.mm"
include "swrdccatin12.mm"
include "sylc.mm"
include "ex.mm"
include "opeq2.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "eqeq2d.mm"
include "sylibd.mm"
include "mpcom.mm"

theorem swrdccatin12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  assume swrdccatind.l: |- ( ph -> ( # ` A ) = L )
  assume swrdccatind.w: |- ( ph -> ( A e. Word V /\ B e. Word V ) )
  assume swrdccatin12d.1: |- ( ph -> M e. ( 0 ... L ) )
  assume swrdccatin12d.2: |- ( ph -> N e. ( L ... ( L + ( # ` B ) ) ) )


  assert |- ( ph -> ( ( A ++ B ) substr <. M , N >. ) = ( ( A substr <. M , L >. ) ++ ( B substr <. 0 , ( N - L ) >. ) ) )

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
    cA
    cM
    cL
    cop
    #
    csubstr
    co
    #
    cB
    cc0
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
    cconcat
    co
    #
    wceq
    #
    swrdccatind.l
    @1
    wph
    @2
    cA
    cM
    @0
    cop
    #
    csubstr
    co
    #
    cB
    cc0
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
    cconcat
    co
    #
    wceq
    #
    @9
    @1
    wph
    @16
    @1
    wph
    wa
    #
    cA
    cV
    cword
    #
    wcel
    cB
    @18
    wcel
    wa
    #
    cM
    cc0
    @0
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
    @16
    wph
    @19
    @1
    swrdccatind.w
    adantl
    @17
    @26
    cM
    cc0
    cL
    cfz
    co
    #
    wcel
    #
    cN
    cL
    cL
    @22
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
    @32
    @1
    wph
    @28
    @31
    swrdccatin12d.1
    swrdccatin12d.2
    jca
    adantl
    @1
    @26
    @32
    wb
    wph
    @1
    @21
    @28
    @25
    @31
    @1
    @20
    @27
    cM
    @0
    cL
    cc0
    cfz
    oveq2
    eleq2d
    @1
    @24
    @30
    cN
    @1
    @0
    cL
    @23
    @29
    cfz
    @1
    id
    @0
    cL
    @22
    caddc
    oveq1
    oveq12d
    eleq2d
    anbi12d
    adantr
    mpbird
    cA
    cB
    @0
    cM
    cN
    cV
    @0
    eqid
    swrdccatin12
    sylc
    ex
    @1
    @15
    @8
    @2
    @1
    @11
    @4
    @14
    @7
    cconcat
    @1
    @10
    @3
    cA
    csubstr
    @0
    cL
    cM
    opeq2
    oveq2d
    @1
    @13
    @6
    cB
    csubstr
    @1
    @12
    @5
    cc0
    @0
    cL
    cN
    cmin
    oveq2
    opeq2d
    oveq2d
    oveq12d
    eqeq2d
    sylibd
    mpcom
end
