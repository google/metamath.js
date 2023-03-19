include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "cuz.mm"
include "cfv.mm"
include "eqid.mm"
include "simpr.mm"
include "snex.mm"
include "xpex.mm"
include "a1i.mm"
include "simpl.mm"
include "cv.mm"
include "wceq.mm"
include "sseli.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "climconst.mm"

theorem climconst2
  let cA: class A
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  assume climconst2.1: |- ( ZZ>= ` M ) C_ Z
  assume climconst2.2: |- Z e. _V


  assert |- ( ( A e. CC /\ M e. ZZ ) -> ( Z X. { A } ) ~~> A )

  proof
    cA
    cc
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    cA
    vk
    cZ
    cA
    csn
    #
    cxp
    #
    cM
    cvv
    cM
    cuz
    cfv
    #
    @5
    eqid
    @0
    @1
    simpr
    @4
    cvv
    wcel
    @2
    cZ
    @3
    climconst2.2
    cA
    snex
    xpex
    a1i
    @0
    @1
    simpl
    #
    @2
    @0
    vk
    cv
    #
    cZ
    wcel
    @7
    @4
    cfv
    cA
    wceq
    @7
    @5
    wcel
    @6
    @5
    cZ
    @7
    climconst2.1
    sseli
    cZ
    cA
    @7
    cc
    fvconst2g
    syl2an
    climconst
end
