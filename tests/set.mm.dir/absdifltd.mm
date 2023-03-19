include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wa.mm"
include "wb.mm"
include "absdiflt.mm"
include "syl3anc.mm"

theorem absdifltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume absltd.1: |- ( ph -> A e. RR )
  assume absltd.2: |- ( ph -> B e. RR )
  assume absltd.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( ( abs ` ( A - B ) ) < C <-> ( ( B - C ) < A /\ A < ( B + C ) ) ) )

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
    cmin
    co
    cabs
    cfv
    cC
    clt
    wbr
    cB
    cC
    cmin
    co
    cA
    clt
    wbr
    cA
    cB
    cC
    caddc
    co
    clt
    wbr
    wa
    wb
    absltd.1
    absltd.2
    absltd.3
    cA
    cB
    cC
    absdiflt
    syl3anc
end
