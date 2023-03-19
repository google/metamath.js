include "wcel.mm"
include "cfv.mm"
include "id.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wb.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ffvelrnda.mm"

theorem fvmap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  assume fvmap.a: |- ( ph -> A e. V )
  assume fvmap.b: |- ( ph -> B e. W )
  assume fvmap.f: |- ( ph -> F e. ( A ^m B ) )
  assume fvmap.c: |- ( ph -> C e. B )


  assert |- ( ph -> ( F ` C ) e. A )

  proof
    wph
    wph
    cC
    cB
    wcel
    cC
    cF
    cfv
    cA
    wcel
    wph
    id
    fvmap.c
    wph
    cB
    cA
    cC
    cF
    wph
    cF
    cA
    cB
    cmap
    co
    wcel
    #
    cB
    cA
    cF
    wf
    #
    fvmap.f
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @0
    @1
    wb
    fvmap.a
    fvmap.b
    cA
    cB
    cF
    cV
    cW
    elmapg
    syl2anc
    mpbid
    ffvelrnda
    syl2anc
end
