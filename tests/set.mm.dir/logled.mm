include "crp.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "wb.mm"
include "logleb.mm"
include "syl2anc.mm"

theorem logled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume relogcld.1: |- ( ph -> A e. RR+ )
  assume relogmuld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A <_ B <-> ( log ` A ) <_ ( log ` B ) ) )

  proof
    wph
    cA
    crp
    wcel
    cB
    crp
    wcel
    cA
    cB
    cle
    wbr
    cA
    clog
    cfv
    cB
    clog
    cfv
    cle
    wbr
    wb
    relogcld.1
    relogmuld.2
    cA
    cB
    logleb
    syl2anc
end
