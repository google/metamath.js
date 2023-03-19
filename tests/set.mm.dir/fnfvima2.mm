include "cin.mm"
include "cima.mm"
include "cfv.mm"
include "wss.mm"
include "inss2.mm"
include "imass2.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wfn.mm"
include "wcel.mm"
include "inss1.mm"
include "elind.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "sseldd.mm"

theorem fnfvima2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fnfvima2.1: |- ( ph -> F Fn A )
  assume fnfvima2.2: |- ( ph -> B e. A )
  assume fnfvima2.3: |- ( ph -> B e. C )


  assert |- ( ph -> ( F ` B ) e. ( F " C ) )

  proof
    wph
    cF
    cA
    cC
    cin
    #
    cima
    #
    cF
    cC
    cima
    #
    cB
    cF
    cfv
    #
    @1
    @2
    wss
    #
    wph
    @0
    cC
    wss
    @4
    cA
    cC
    inss2
    @0
    cC
    cF
    imass2
    ax-mp
    a1i
    wph
    cF
    cA
    wfn
    @0
    cA
    wss
    #
    cB
    @0
    wcel
    @3
    @1
    wcel
    fnfvima2.1
    @5
    wph
    cA
    cC
    inss1
    a1i
    wph
    cA
    cC
    cB
    fnfvima2.2
    fnfvima2.3
    elind
    cA
    @0
    cF
    cB
    fnfvima
    syl3anc
    sseldd
end
