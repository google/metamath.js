include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cdiv.mm"
include "co.mm"
include "jca.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "lediv12a.mm"
include "syl22anc.mm"

theorem lediv12ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )
  assume lediv12ad.4: |- ( ph -> D e. RR )
  assume lediv12ad.5: |- ( ph -> 0 <_ A )
  assume lediv12ad.6: |- ( ph -> A <_ B )
  assume lediv12ad.7: |- ( ph -> C <_ D )


  assert |- ( ph -> ( A / D ) <_ ( B / C ) )

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
    cle
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
    clt
    wbr
    #
    cC
    cD
    cle
    wbr
    #
    wa
    cA
    cD
    cdiv
    co
    cB
    cC
    cdiv
    co
    cle
    wbr
    wph
    @0
    @1
    ltmul1d.1
    ltmul1d.2
    jca
    wph
    @2
    @3
    lediv12ad.5
    lediv12ad.6
    jca
    wph
    @4
    @5
    wph
    cC
    ltmul1d.3
    rpred
    lediv12ad.4
    jca
    wph
    @6
    @7
    wph
    cC
    ltmul1d.3
    rpgt0d
    lediv12ad.7
    jca
    cA
    cB
    cC
    cD
    lediv12a
    syl22anc
end
