include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "wb.mm"
include "abslt.mm"
include "syl2anc.mm"

theorem absltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume absltd.1: |- ( ph -> A e. RR )
  assume absltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( ( abs ` A ) < B <-> ( -u B < A /\ A < B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cabs
    cfv
    cB
    clt
    wbr
    cB
    cneg
    cA
    clt
    wbr
    cA
    cB
    clt
    wbr
    wa
    wb
    absltd.1
    absltd.2
    cA
    cB
    abslt
    syl2anc
end
