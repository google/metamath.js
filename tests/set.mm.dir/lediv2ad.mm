include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "cdiv.mm"
include "co.mm"
include "rpregt0d.mm"
include "jca.mm"
include "lediv2a.mm"
include "syl31anc.mm"

theorem lediv2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )
  assume lediv2ad.3: |- ( ph -> C e. RR )
  assume lediv2ad.4: |- ( ph -> 0 <_ C )
  assume lediv2ad.5: |- ( ph -> A <_ B )


  assert |- ( ph -> ( C / B ) <_ ( C / A ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
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
    cB
    cdiv
    co
    cC
    cA
    cdiv
    co
    cle
    wbr
    wph
    cA
    rpred.1
    rpregt0d
    wph
    cB
    rpaddcld.1
    rpregt0d
    wph
    @0
    @1
    lediv2ad.3
    lediv2ad.4
    jca
    lediv2ad.5
    cA
    cB
    cC
    lediv2a
    syl31anc
end
