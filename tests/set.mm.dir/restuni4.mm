include "cuni.mm"
include "cin.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "wss.mm"
include "dfss.mm"
include "sylib.mm"
include "cvv.mm"
include "uniexd.mm"
include "ssexd.mm"
include "restuni3.mm"
include "3eqtr4rd.mm"

theorem restuni4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  assume restuni4.1: |- ( ph -> A e. V )
  assume restuni4.2: |- ( ph -> B C_ U. A )


  assert |- ( ph -> U. ( A |`t B ) = B )

  proof
    wph
    cB
    cA
    cuni
    #
    cin
    #
    @0
    cB
    cin
    #
    cB
    cA
    cB
    crest
    co
    cuni
    @1
    @2
    wceq
    wph
    cB
    @0
    incom
    a1i
    wph
    cB
    @0
    wss
    cB
    @1
    wceq
    restuni4.2
    cB
    @0
    dfss
    sylib
    wph
    cA
    cB
    cV
    cvv
    restuni4.1
    wph
    cB
    @0
    cvv
    wph
    cA
    cV
    restuni4.1
    uniexd
    restuni4.2
    ssexd
    restuni3
    3eqtr4rd
end
