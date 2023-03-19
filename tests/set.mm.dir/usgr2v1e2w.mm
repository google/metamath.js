include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "cs1.mm"
include "cop.mm"
include "cc0.mm"
include "csn.mm"
include "cusgr.mm"
include "cvv.mm"
include "wceq.mm"
include "prex.mm"
include "s1val.mm"
include "mp1i.mm"
include "opeq2d.mm"
include "wa.mm"
include "prid1g.mm"
include "prid2g.mm"
include "anim12i.mm"
include "c0ex.mm"
include "pm3.2i.mm"
include "jctil.mm"
include "usgr1eop.mm"
include "imp.mm"
include "stoic3.mm"
include "eqeltrd.mm"

theorem usgr2v1e2w
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( A e. X /\ B e. Y /\ A =/= B ) -> <. { A , B } , <" { A , B } "> >. e. USGraph )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cpr
    #
    @4
    cs1
    #
    cop
    @4
    cc0
    @4
    cop
    csn
    #
    cop
    #
    cusgr
    @3
    @5
    @6
    @4
    @4
    cvv
    wcel
    #
    @5
    @6
    wceq
    @3
    cA
    cB
    prex
    #
    @4
    cvv
    s1val
    mp1i
    opeq2d
    @0
    @1
    @8
    cc0
    cvv
    wcel
    #
    wa
    #
    cA
    @4
    wcel
    #
    cB
    @4
    wcel
    #
    wa
    #
    wa
    #
    @2
    @7
    cusgr
    wcel
    #
    @0
    @1
    wa
    @14
    @11
    @0
    @12
    @1
    @13
    cA
    cB
    cX
    prid1g
    cA
    cB
    cY
    prid2g
    anim12i
    @8
    @10
    @9
    c0ex
    pm3.2i
    jctil
    @15
    @2
    @16
    cc0
    cA
    cB
    @4
    cvv
    cvv
    usgr1eop
    imp
    stoic3
    eqeltrd
end
