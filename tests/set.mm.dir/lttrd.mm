include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem lttrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume letrd.3: |- ( ph -> C e. RR )
  assume lttrd.4: |- ( ph -> A < B )
  assume lttrd.5: |- ( ph -> B < C )


  assert |- ( ph -> A < C )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    lttrd.4
    lttrd.5
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    @0
    @1
    wa
    @2
    wi
    ltd.1
    ltd.2
    letrd.3
    cA
    cB
    cC
    lttr
    syl3anc
    mp2and
end
