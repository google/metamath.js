include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "jca.mm"
include "lemul1a.mm"
include "syl31anc.mm"

theorem lemul1ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume lemul1ad.3: |- ( ph -> C e. RR )
  assume lemul1ad.4: |- ( ph -> 0 <_ C )
  assume lemul1ad.5: |- ( ph -> A <_ B )


  assert |- ( ph -> ( A x. C ) <_ ( B x. C ) )

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
    #
    cc0
    cC
    cle
    wbr
    #
    wa
    cA
    cB
    cle
    wbr
    cA
    cC
    cmul
    co
    cB
    cC
    cmul
    co
    cle
    wbr
    ltp1d.1
    divgt0d.2
    wph
    @0
    @1
    lemul1ad.3
    lemul1ad.4
    jca
    lemul1ad.5
    cA
    cB
    cC
    lemul1a
    syl31anc
end
