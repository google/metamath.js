include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "jca.mm"
include "lemul2a.mm"
include "syl31anc.mm"

theorem lemul2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume lemul1ad.3: |- ( ph -> C e. RR )
  assume lemul1ad.4: |- ( ph -> 0 <_ C )
  assume lemul1ad.5: |- ( ph -> A <_ B )


  assert |- ( ph -> ( C x. A ) <_ ( C x. B ) )

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
    cC
    cA
    cmul
    co
    cC
    cB
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
    lemul2a
    syl31anc
end
