include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "msqgt0.mm"
include "syl2anc.mm"

theorem msqgt0d
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )
  assume msqgt0d.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> 0 < ( A x. A ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    wne
    cc0
    cA
    cA
    cmul
    co
    clt
    wbr
    leidd.1
    msqgt0d.2
    cA
    msqgt0
    syl2anc
end
