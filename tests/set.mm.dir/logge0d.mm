include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "clog.mm"
include "cfv.mm"
include "logge0.mm"
include "syl2anc.mm"

theorem logge0d
  let wph: wff ph
  let cA: class A
  assume relogefd.1: |- ( ph -> A e. RR )
  assume logge0d.2: |- ( ph -> 1 <_ A )


  assert |- ( ph -> 0 <_ ( log ` A ) )

  proof
    wph
    cA
    cr
    wcel
    c1
    cA
    cle
    wbr
    cc0
    cA
    clog
    cfv
    cle
    wbr
    relogefd.1
    logge0d.2
    cA
    logge0
    syl2anc
end
