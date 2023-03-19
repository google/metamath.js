include "cin.mm"
include "cima.mm"
include "cfv.mm"
include "wss.mm"
include "inss2.mm"
include "imass2.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "wcel.mm"
include "wfn.mm"
include "fnfun.mm"
include "syl.mm"
include "inss1.mm"
include "fndmd.mm"
include "sseqtr4d.mm"
include "jca.mm"
include "elind.mm"
include "funfvima2.mm"
include "sylc.mm"
include "sseldd.mm"

theorem fnfvimad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fnfvimad.1: |- ( ph -> F Fn A )
  assume fnfvimad.2: |- ( ph -> B e. A )
  assume fnfvimad.3: |- ( ph -> B e. C )


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
    wfun
    #
    @0
    cF
    cdm
    #
    wss
    #
    wa
    cB
    @0
    wcel
    @3
    @1
    wcel
    wph
    @5
    @7
    wph
    cF
    cA
    wfn
    @5
    fnfvimad.1
    cA
    cF
    fnfun
    syl
    wph
    @0
    cA
    @6
    @0
    cA
    wss
    wph
    cA
    cC
    inss1
    a1i
    wph
    cA
    cF
    fnfvimad.1
    fndmd
    sseqtr4d
    jca
    wph
    cA
    cC
    cB
    fnfvimad.2
    fnfvimad.3
    elind
    @0
    cB
    cF
    funfvima2
    sylc
    sseldd
end
