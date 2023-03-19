include "ccnv.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "jca.mm"
include "wfn.mm"
include "wb.mm"
include "elpreima.mm"
include "syl.mm"
include "mpbird.mm"

theorem elpreimad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume elpreimad.f: |- ( ph -> F Fn A )
  assume elpreimad.b: |- ( ph -> B e. A )
  assume elpreimad.c: |- ( ph -> ( F ` B ) e. C )


  assert |- ( ph -> B e. ( `' F " C ) )

  proof
    wph
    cB
    cF
    ccnv
    cC
    cima
    wcel
    #
    cB
    cA
    wcel
    #
    cB
    cF
    cfv
    cC
    wcel
    #
    wa
    #
    wph
    @1
    @2
    elpreimad.b
    elpreimad.c
    jca
    wph
    cF
    cA
    wfn
    @0
    @3
    wb
    elpreimad.f
    cA
    cB
    cC
    cF
    elpreima
    syl
    mpbird
end
