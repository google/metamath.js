include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "jca.mm"
include "ltmul12a.mm"
include "syl22anc.mm"

theorem ltmul12ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume lemul1ad.3: |- ( ph -> C e. RR )
  assume ltmul12ad.3: |- ( ph -> D e. RR )
  assume ltmul12ad.4: |- ( ph -> 0 <_ A )
  assume ltmul12ad.5: |- ( ph -> A < B )
  assume ltmul12ad.6: |- ( ph -> 0 <_ C )
  assume ltmul12ad.7: |- ( ph -> C < D )


  assert |- ( ph -> ( A x. C ) < ( B x. D ) )

  proof
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wa
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    cc0
    cC
    cle
    wbr
    #
    cC
    cD
    clt
    wbr
    #
    wa
    cA
    cC
    cmul
    co
    cB
    cD
    cmul
    co
    clt
    wbr
    wph
    @0
    @1
    ltp1d.1
    divgt0d.2
    jca
    wph
    @2
    @3
    ltmul12ad.4
    ltmul12ad.5
    jca
    wph
    @4
    @5
    lemul1ad.3
    ltmul12ad.3
    jca
    wph
    @6
    @7
    ltmul12ad.6
    ltmul12ad.7
    jca
    cA
    cB
    cC
    cD
    ltmul12a
    syl22anc
end
