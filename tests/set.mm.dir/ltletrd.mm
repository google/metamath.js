include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem ltletrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume letrd.3: |- ( ph -> C e. RR )
  assume ltletrd.4: |- ( ph -> A < B )
  assume ltletrd.5: |- ( ph -> B <_ C )


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
    cle
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    ltletrd.4
    ltletrd.5
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
    ltletr
    syl3anc
    mp2and
end
