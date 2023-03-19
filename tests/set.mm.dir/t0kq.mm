include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ct0.mm"
include "ckq.mm"
include "chmeo.mm"
include "co.mm"
include "wa.mm"
include "cqtop.mm"
include "cvv.mm"
include "simpl.mm"
include "wf1.mm"
include "ist0-4.mm"
include "biimpa.mm"
include "qtopf1.mm"
include "wceq.mm"
include "kqval.mm"
include "adantr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "chmph.mm"
include "wbr.mm"
include "hmphi.mm"
include "hmphsym.mm"
include "syl.mm"
include "kqt0lem.mm"
include "t0hmph.mm"
include "syl2im.mm"
include "impcom.mm"
include "impbida.mm"

theorem t0kq
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cX: class X
  assume t0kq.1: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Kol2 <-> F e. ( J Homeo ( KQ ` J ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ct0
    wcel
    #
    cF
    cJ
    cJ
    ckq
    cfv
    #
    chmeo
    co
    #
    wcel
    #
    @0
    @1
    wa
    #
    cF
    cJ
    cJ
    cF
    cqtop
    co
    #
    chmeo
    co
    @3
    @5
    cF
    cJ
    cX
    cvv
    @0
    @1
    simpl
    @0
    @1
    cX
    cvv
    cF
    wf1
    vx
    vy
    cF
    cJ
    cX
    t0kq.1
    ist0-4
    biimpa
    qtopf1
    @5
    @2
    @6
    cJ
    chmeo
    @0
    @2
    @6
    wceq
    @1
    vx
    vy
    cF
    cJ
    cX
    t0kq.1
    kqval
    adantr
    oveq2d
    eleqtrrd
    @4
    @0
    @1
    @4
    @2
    cJ
    chmph
    wbr
    #
    @0
    @2
    ct0
    wcel
    @1
    @4
    cJ
    @2
    chmph
    wbr
    @7
    cF
    cJ
    @2
    hmphi
    cJ
    @2
    hmphsym
    syl
    vx
    vy
    cF
    cJ
    cX
    t0kq.1
    kqt0lem
    @2
    cJ
    t0hmph
    syl2im
    impcom
    impbida
end
