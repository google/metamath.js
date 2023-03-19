include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "mulgt0.mm"
include "syl22anc.mm"

theorem mulgt0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume mulgt0d.3: |- ( ph -> 0 < A )
  assume mulgt0d.4: |- ( ph -> 0 < B )


  assert |- ( ph -> 0 < ( A x. B ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    cc0
    cA
    cB
    cmul
    co
    clt
    wbr
    ltd.1
    mulgt0d.3
    ltd.2
    mulgt0d.4
    cA
    cB
    mulgt0
    syl22anc
end
