include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "lemulge12.mm"
include "syl22anc.mm"

theorem lemulge12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume lemulge11d.3: |- ( ph -> 0 <_ A )
  assume lemulge11d.4: |- ( ph -> 1 <_ B )


  assert |- ( ph -> A <_ ( B x. A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    cle
    wbr
    c1
    cB
    cle
    wbr
    cA
    cB
    cA
    cmul
    co
    cle
    wbr
    ltp1d.1
    divgt0d.2
    lemulge11d.3
    lemulge11d.4
    cA
    cB
    lemulge12
    syl22anc
end
