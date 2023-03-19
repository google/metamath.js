include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "ltadd2.mm"
include "syl3anc.mm"

theorem ltadd2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume letrd.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( A < B <-> ( C + A ) < ( C + B ) ) )

  proof
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
    cA
    cB
    clt
    wbr
    cC
    cA
    caddc
    co
    cC
    cB
    caddc
    co
    clt
    wbr
    wb
    ltd.1
    ltd.2
    letrd.3
    cA
    cB
    cC
    ltadd2
    syl3anc
end
