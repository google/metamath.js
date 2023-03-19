include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cc.mm"
include "eldifsn.mm"
include "wf.mm"
include "adantr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "subcld.mm"
include "wss.mm"
include "sseldd.mm"
include "simprr.mm"
include "subne0d.mm"
include "divcld.mm"
include "sylan2b.mm"

theorem dvlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  assume dvlem.1: |- ( ph -> F : D --> CC )
  assume dvlem.2: |- ( ph -> D C_ CC )
  assume dvlem.3: |- ( ph -> B e. D )


  assert |- ( ( ph /\ A e. ( D \ { B } ) ) -> ( ( ( F ` A ) - ( F ` B ) ) / ( A - B ) ) e. CC )

  proof
    cA
    cD
    cB
    csn
    cdif
    wcel
    wph
    cA
    cD
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cmin
    co
    #
    cA
    cB
    cmin
    co
    #
    cdiv
    co
    cc
    wcel
    cA
    cD
    cB
    eldifsn
    wph
    @2
    wa
    #
    @5
    @6
    @7
    @3
    @4
    @7
    cD
    cc
    cA
    cF
    wph
    cD
    cc
    cF
    wf
    @2
    dvlem.1
    adantr
    #
    wph
    @0
    @1
    simprl
    #
    ffvelrnd
    @7
    cD
    cc
    cB
    cF
    @8
    wph
    cB
    cD
    wcel
    @2
    dvlem.3
    adantr
    #
    ffvelrnd
    subcld
    @7
    cA
    cB
    @7
    cD
    cc
    cA
    wph
    cD
    cc
    wss
    @2
    dvlem.2
    adantr
    #
    @9
    sseldd
    #
    @7
    cD
    cc
    cB
    @11
    @10
    sseldd
    #
    subcld
    @7
    cA
    cB
    @12
    @13
    wph
    @0
    @1
    simprr
    subne0d
    divcld
    sylan2b
end
