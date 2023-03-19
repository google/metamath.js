include "co.mm"
include "cmpt.mm"
include "crest.mm"
include "ccn.mm"
include "cc.mm"
include "ccncf.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "cncfrss.mm"
include "syl.mm"
include "resttopon.mm"
include "sylancr.mm"
include "wceq.mm"
include "ssid.mm"
include "eqid.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "sylancl.mm"
include "eleqtrd.mm"
include "cnmpt12f.mm"
include "eleqtrrd.mm"

theorem cncfmpt2f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cX: class X
  assume cncfmpt2f.1: |- J = ( TopOpen ` CCfld )
  assume cncfmpt2f.2: |- ( ph -> F e. ( ( J tX J ) Cn J ) )
  assume cncfmpt2f.3: |- ( ph -> ( x e. X |-> A ) e. ( X -cn-> CC ) )
  assume cncfmpt2f.4: |- ( ph -> ( x e. X |-> B ) e. ( X -cn-> CC ) )

  disjoint F x
  disjoint J x
  disjoint ph x
  disjoint X x
  assert |- ( ph -> ( x e. X |-> ( A F B ) ) e. ( X -cn-> CC ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cF
    co
    cmpt
    cJ
    cX
    crest
    co
    #
    cJ
    ccn
    co
    #
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    cA
    cB
    cF
    @0
    cJ
    cJ
    cJ
    cX
    wph
    cJ
    cc
    ctopon
    cfv
    #
    wcel
    #
    cX
    cc
    wss
    #
    @0
    cX
    ctopon
    cfv
    wcel
    cJ
    cncfmpt2f.1
    cnfldtopon
    #
    wph
    vx
    cX
    cA
    cmpt
    #
    @2
    wcel
    @5
    cncfmpt2f.3
    cX
    cc
    @7
    cncfrss
    syl
    #
    cX
    cJ
    cc
    resttopon
    sylancr
    wph
    @7
    @2
    @1
    cncfmpt2f.3
    wph
    @5
    cc
    cc
    wss
    @2
    @1
    wceq
    @8
    cc
    ssid
    cX
    cc
    cJ
    @0
    cJ
    cncfmpt2f.1
    @0
    eqid
    cJ
    cc
    crest
    co
    #
    cJ
    @4
    @9
    cJ
    wceq
    @6
    cJ
    @3
    cc
    cc
    cJ
    @6
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    sylancl
    #
    eleqtrd
    wph
    vx
    cX
    cB
    cmpt
    @2
    @1
    cncfmpt2f.4
    @10
    eleqtrd
    cncfmpt2f.2
    cnmpt12f
    @10
    eleqtrrd
end
