include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "wb.mm"
include "absle.mm"
include "syl2anc.mm"

theorem absled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume absltd.1: |- ( ph -> A e. RR )
  assume absltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( ( abs ` A ) <_ B <-> ( -u B <_ A /\ A <_ B ) ) )

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
    cle
    wbr
    cB
    cneg
    cA
    cle
    wbr
    cA
    cB
    cle
    wbr
    wa
    wb
    absltd.1
    absltd.2
    cA
    cB
    absle
    syl2anc
end
