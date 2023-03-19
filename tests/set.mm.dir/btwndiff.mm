include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wa.mm"
include "axlowdim1.mm"
include "3ad2ant1.mm"
include "ccgr.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "axsegcon.mm"
include "syl122anc.mm"
include "wceq.mm"
include "weq.mm"
include "wb.mm"
include "wi.mm"
include "simpl11.mm"
include "simpl13.mm"
include "simpr.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "cgrdegen.mm"
include "biimp.mm"
include "necon3d.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "syld.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdvv.mm"

theorem btwndiff
  let cA: class A
  let cB: class B
  let cN: class N
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v

  disjoint A c
  disjoint B c
  disjoint N c
  disjoint A u
  disjoint A v
  disjoint c u
  disjoint c v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint N u
  disjoint N v
  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> E. c e. ( EE ` N ) ( B Btwn <. A , c >. /\ B =/= c ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    vu
    cv
    #
    vv
    cv
    #
    wne
    #
    vv
    @1
    wrex
    vu
    @1
    wrex
    #
    cB
    cA
    vc
    cv
    #
    cop
    cbtwn
    wbr
    #
    cB
    @9
    wne
    #
    wa
    #
    vc
    @1
    wrex
    #
    @0
    @2
    @8
    @3
    vu
    vv
    cN
    axlowdim1
    3ad2ant1
    @4
    @7
    @13
    vu
    vv
    @1
    @1
    @4
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    @7
    @13
    @4
    @16
    @7
    w3a
    #
    @10
    cB
    @9
    cop
    @5
    @6
    cop
    ccgr
    wbr
    #
    wa
    #
    vc
    @1
    wrex
    #
    @13
    @17
    @0
    @2
    @3
    @14
    @15
    @20
    @0
    @2
    @3
    @16
    @7
    simp11
    @0
    @2
    @3
    @16
    @7
    simp12
    @0
    @2
    @3
    @16
    @7
    simp13
    @4
    @14
    @15
    @7
    simp2l
    @4
    @14
    @15
    @7
    simp2r
    vc
    cA
    cB
    @5
    @6
    cN
    axsegcon
    syl122anc
    @17
    @19
    @12
    vc
    @1
    @17
    @9
    @1
    wcel
    #
    wa
    #
    @18
    @11
    @10
    @22
    @18
    cB
    @9
    wceq
    #
    vu
    vv
    weq
    #
    wb
    #
    @11
    @22
    @0
    @3
    @21
    @14
    @15
    @18
    @25
    wi
    @0
    @2
    @3
    @16
    @7
    @21
    simpl11
    @0
    @2
    @3
    @16
    @7
    @21
    simpl13
    @17
    @21
    simpr
    @14
    @15
    @4
    @7
    @21
    simpl2l
    @14
    @15
    @4
    @7
    @21
    simpl2r
    cB
    @9
    @5
    @6
    cN
    cgrdegen
    syl122anc
    @17
    @25
    @11
    wi
    #
    @21
    @7
    @4
    @26
    @16
    @25
    @7
    @11
    @25
    cB
    @9
    @5
    @6
    @23
    @24
    biimp
    necon3d
    com12
    3ad2ant3
    adantr
    syld
    anim2d
    reximdva
    mpd
    3exp
    rexlimdvv
    mpd
end
