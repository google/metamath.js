include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "wne.mm"
include "ismri2d.mm"
include "wa.mm"
include "cmre.mm"
include "adantr.mm"
include "wss.mm"
include "simpr.mm"
include "mrieqvlemd.mm"
include "necon3bbid.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem mrieqvd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  assume mrieqvd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrieqvd.2: |- N = ( mrCls ` A )
  assume mrieqvd.3: |- I = ( mrInd ` A )
  assume mrieqvd.4: |- ( ph -> S C_ X )

  disjoint A x
  disjoint S x
  disjoint ph x
  assert |- ( ph -> ( S e. I <-> A. x e. S ( N ` ( S \ { x } ) ) =/= ( N ` S ) ) )

  proof
    wph
    cS
    cI
    wcel
    vx
    cv
    #
    cS
    @0
    csn
    cdif
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cS
    wral
    @1
    cS
    cN
    cfv
    #
    wne
    #
    vx
    cS
    wral
    wph
    vx
    cA
    cS
    cI
    cN
    cX
    mrieqvd.2
    mrieqvd.3
    mrieqvd.1
    mrieqvd.4
    ismri2d
    wph
    @3
    @5
    vx
    cS
    wph
    @0
    cS
    wcel
    #
    wa
    #
    @2
    @1
    @4
    @7
    cA
    cS
    cN
    cX
    @0
    wph
    cA
    cX
    cmre
    cfv
    wcel
    @6
    mrieqvd.1
    adantr
    mrieqvd.2
    wph
    cS
    cX
    wss
    @6
    mrieqvd.4
    adantr
    wph
    @6
    simpr
    mrieqvlemd
    necon3bbid
    ralbidva
    bitrd
end
