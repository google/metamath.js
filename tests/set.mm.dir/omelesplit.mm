include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wceq.mm"
include "inundif.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq2d.mm"
include "wss.mm"
include "ssinss1.mm"
include "syl.mm"
include "ssdifssd.mm"
include "omeunle.mm"
include "eqbrtrd.mm"

theorem omelesplit
  let wph: wff ph
  let cA: class A
  let cE: class E
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omelesplit.1: |- ( ph -> O e. OutMeas )
  assume omelesplit.2: |- X = U. dom O
  assume omelesplit.3: |- ( ph -> A C_ X )


  assert |- ( ph -> ( O ` A ) <_ ( ( O ` ( A i^i E ) ) +e ( O ` ( A \ E ) ) ) )

  proof
    wph
    cA
    cO
    cfv
    cA
    cE
    cin
    #
    cA
    cE
    cdif
    #
    cun
    #
    cO
    cfv
    @0
    cO
    cfv
    @1
    cO
    cfv
    cxad
    co
    cle
    wph
    cA
    @2
    cO
    cA
    @2
    wceq
    wph
    @2
    cA
    cA
    cE
    inundif
    eqcomi
    a1i
    fveq2d
    wph
    @0
    @1
    cO
    cX
    omelesplit.1
    omelesplit.2
    wph
    cA
    cX
    wss
    @0
    cX
    wss
    omelesplit.3
    cA
    cE
    cX
    ssinss1
    syl
    wph
    cA
    cX
    cE
    omelesplit.3
    ssdifssd
    omeunle
    eqbrtrd
end
