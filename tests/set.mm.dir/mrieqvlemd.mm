include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cmre.mm"
include "adantr.mm"
include "cun.mm"
include "undif1.mm"
include "wss.mm"
include "ssdifssd.mm"
include "mrcssidd.mm"
include "simpr.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqssr.mm"
include "unssad.mm"
include "difssd.mm"
include "mressmrcd.mm"
include "eqcomd.mm"
include "sseldd.mm"
include "eleqtrrd.mm"
include "impbida.mm"

theorem mrieqvlemd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cN: class N
  let cX: class X
  let cY: class Y
  assume mrieqvlemd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrieqvlemd.2: |- N = ( mrCls ` A )
  assume mrieqvlemd.3: |- ( ph -> S C_ X )
  assume mrieqvlemd.4: |- ( ph -> Y e. S )


  assert |- ( ph -> ( Y e. ( N ` ( S \ { Y } ) ) <-> ( N ` ( S \ { Y } ) ) = ( N ` S ) ) )

  proof
    wph
    cY
    cS
    cY
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    @2
    cS
    cN
    cfv
    #
    wceq
    #
    wph
    @3
    wa
    #
    @4
    @2
    @6
    cA
    cS
    @1
    cN
    cX
    wph
    cA
    cX
    cmre
    cfv
    wcel
    @3
    mrieqvlemd.1
    adantr
    #
    mrieqvlemd.2
    @6
    cS
    @0
    @2
    @6
    cS
    @0
    cun
    @1
    @0
    cun
    @2
    cS
    @0
    undif1
    @6
    @1
    @0
    @2
    @6
    cA
    @1
    cN
    cX
    @7
    mrieqvlemd.2
    @6
    cS
    cX
    @0
    wph
    cS
    cX
    wss
    @3
    mrieqvlemd.3
    adantr
    ssdifssd
    mrcssidd
    @6
    cY
    @2
    wph
    @3
    simpr
    snssd
    unssd
    syl5eqssr
    unssad
    @6
    cS
    @0
    difssd
    mressmrcd
    eqcomd
    wph
    @5
    wa
    cY
    @4
    @2
    wph
    cY
    @4
    wcel
    @5
    wph
    cS
    @4
    cY
    wph
    cA
    cS
    cN
    cX
    mrieqvlemd.1
    mrieqvlemd.2
    mrieqvlemd.3
    mrcssidd
    mrieqvlemd.4
    sseldd
    adantr
    wph
    @5
    simpr
    eleqtrrd
    impbida
end
