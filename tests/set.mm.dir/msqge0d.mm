include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "msqge0.mm"
include "syl.mm"

theorem msqge0d
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> 0 <_ ( A x. A ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cA
    cmul
    co
    cle
    wbr
    leidd.1
    cA
    msqge0
    syl
end
