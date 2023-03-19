include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "cr.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "supgtoreq.mm"
include "sseldd.mm"
include "csup.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ne0i.mm"
include "syl.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "eqeltrd.mm"
include "leloed.mm"
include "mpbird.mm"

theorem supfirege
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  assume supfirege.1: |- ( ph -> B C_ RR )
  assume supfirege.2: |- ( ph -> B e. Fin )
  assume supfirege.3: |- ( ph -> C e. B )
  assume supfirege.4: |- ( ph -> S = sup ( B , RR , < ) )


  assert |- ( ph -> C <_ S )

  proof
    wph
    cC
    cS
    cle
    wbr
    cC
    cS
    clt
    wbr
    cC
    cS
    wceq
    wo
    wph
    cr
    cB
    cC
    clt
    cS
    cr
    clt
    wor
    #
    wph
    ltso
    a1i
    #
    supfirege.1
    supfirege.2
    supfirege.3
    supfirege.4
    supgtoreq
    wph
    cC
    cS
    wph
    cB
    cr
    cC
    supfirege.1
    supfirege.3
    sseldd
    wph
    cB
    cr
    cS
    supfirege.1
    wph
    cS
    cB
    cr
    clt
    csup
    #
    cB
    supfirege.4
    wph
    @0
    cB
    cfn
    wcel
    cB
    c0
    wne
    #
    cB
    cr
    wss
    @2
    cB
    wcel
    @1
    supfirege.2
    wph
    cC
    cB
    wcel
    @3
    supfirege.3
    cB
    cC
    ne0i
    syl
    supfirege.1
    cr
    cB
    clt
    fisupcl
    syl13anc
    eqeltrd
    sseldd
    leloed
    mpbird
end
