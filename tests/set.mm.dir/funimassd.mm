include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfun.mm"
include "adantr.mm"
include "simpr.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "id.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ssd.mm"

theorem funimassd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume funimassd.1: |- F/ x ph
  assume funimassd.2: |- ( ph -> Fun F )
  assume funimassd.3: |- ( ( ph /\ x e. A ) -> ( F ` x ) e. B )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> ( F " A ) C_ B )

  proof
    wph
    vy
    cF
    cA
    cima
    #
    cB
    wph
    vy
    cv
    #
    @0
    wcel
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    wceq
    #
    vx
    cA
    wrex
    #
    @1
    cB
    wcel
    #
    @3
    cF
    wfun
    #
    @2
    @7
    wph
    @9
    @2
    funimassd.2
    adantr
    wph
    @2
    simpr
    vx
    @1
    cA
    cF
    fvelima
    syl2anc
    @3
    @6
    @8
    vx
    cA
    wph
    @2
    vx
    funimassd.1
    @2
    vx
    nfv
    nfan
    @8
    vx
    nfv
    wph
    @4
    cA
    wcel
    #
    @6
    @8
    wi
    wi
    @2
    wph
    @10
    @6
    @8
    wph
    @10
    @6
    w3a
    @1
    @5
    cB
    @6
    wph
    @1
    @5
    wceq
    @10
    @6
    @5
    @1
    @6
    id
    eqcomd
    3ad2ant3
    wph
    @10
    @5
    cB
    wcel
    @6
    funimassd.3
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    ssd
end
