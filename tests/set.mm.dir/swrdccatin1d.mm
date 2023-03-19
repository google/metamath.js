include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "jca.mm"
include "swrdccatin1.mm"
include "sylc.mm"

theorem swrdccatin1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  assume swrdccatind.l: |- ( ph -> ( # ` A ) = L )
  assume swrdccatind.w: |- ( ph -> ( A e. Word V /\ B e. Word V ) )
  assume swrdccatin1d.1: |- ( ph -> M e. ( 0 ... N ) )
  assume swrdccatin1d.2: |- ( ph -> N e. ( 0 ... L ) )


  assert |- ( ph -> ( ( A ++ B ) substr <. M , N >. ) = ( A substr <. M , N >. ) )

  proof
    wph
    cA
    cV
    cword
    #
    wcel
    cB
    @0
    wcel
    wa
    cM
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
    cA
    cB
    cconcat
    co
    cM
    cN
    cop
    #
    csubstr
    co
    cA
    @5
    csubstr
    co
    wceq
    swrdccatind.w
    wph
    @1
    @4
    swrdccatin1d.1
    @2
    cL
    wceq
    #
    wph
    @4
    swrdccatind.l
    wph
    @4
    @6
    cN
    cc0
    cL
    cfz
    co
    #
    wcel
    swrdccatin1d.2
    @6
    @3
    @7
    cN
    @2
    cL
    cc0
    cfz
    oveq2
    eleq2d
    syl5ibr
    mpcom
    jca
    cA
    cB
    cM
    cN
    cV
    swrdccatin1
    sylc
end
