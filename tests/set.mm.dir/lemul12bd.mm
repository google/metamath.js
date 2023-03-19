include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wa.mm"
include "wi.mm"
include "jca.mm"
include "lemul12b.mm"
include "syl22anc.mm"
include "mp2and.mm"

theorem lemul12bd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume lemul1ad.3: |- ( ph -> C e. RR )
  assume ltmul12ad.3: |- ( ph -> D e. RR )
  assume lemul12bd.4: |- ( ph -> 0 <_ A )
  assume lemul12bd.5: |- ( ph -> 0 <_ D )
  assume lemul12bd.6: |- ( ph -> A <_ B )
  assume lemul12bd.7: |- ( ph -> C <_ D )


  assert |- ( ph -> ( A x. C ) <_ ( B x. D ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cC
    cD
    cle
    wbr
    #
    cA
    cC
    cmul
    co
    cB
    cD
    cmul
    co
    cle
    wbr
    #
    lemul12bd.6
    lemul12bd.7
    wph
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    cB
    cr
    wcel
    cC
    cr
    wcel
    cD
    cr
    wcel
    #
    cc0
    cD
    cle
    wbr
    #
    wa
    @0
    @1
    wa
    @2
    wi
    wph
    @3
    @4
    ltp1d.1
    lemul12bd.4
    jca
    divgt0d.2
    lemul1ad.3
    wph
    @5
    @6
    ltmul12ad.3
    lemul12bd.5
    jca
    cA
    cB
    cC
    cD
    lemul12b
    syl22anc
    mp2and
end
