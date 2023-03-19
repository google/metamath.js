include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "cumgr.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "simpl.mm"
include "simpr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wo.mm"
include "wi.mm"
include "eqid.mm"
include "umgrpredgv.mm"
include "ex.mm"
include "anim12d.mm"
include "adantr.mm"
include "imp.mm"
include "simplr.mm"
include "umgredgne.mm"
include "necomd.mm"
include "ad2ant2r.mm"
include "jca.mm"
include "olcd.mm"
include "prneimg.mm"
include "prid1g.mm"
include "ad3antrrr.mm"
include "prid2g.mm"
include "3jca.mm"
include "syl2anc.mm"
include "wceq.mm"
include "neeq1.mm"
include "eleq2.mm"
include "3anbi12d.mm"
include "neeq2.mm"
include "3anbi13d.mm"
include "rspc2ev.mm"
include "syl2an23an.mm"

theorem umgrvad2edg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cN: class N
  assume umgrvad2edg.e: |- E = ( Edg ` G )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint E x
  disjoint E y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  assert |- ( ( ( G e. UMGraph /\ A =/= B ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> E. x e. E E. y e. E ( x =/= y /\ N e. x /\ N e. y ) )

  proof
    cN
    cA
    cpr
    #
    cE
    wcel
    #
    cB
    cN
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @1
    @3
    cG
    cumgr
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    @0
    @2
    wne
    #
    cN
    @0
    wcel
    #
    cN
    @2
    wcel
    #
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    cN
    @12
    wcel
    #
    cN
    @13
    wcel
    #
    w3a
    #
    vy
    cE
    wrex
    vx
    cE
    wrex
    @1
    @3
    simpl
    @1
    @3
    simpr
    @7
    @4
    wa
    #
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    cA
    @19
    wcel
    #
    wa
    #
    cB
    @19
    wcel
    @20
    wa
    #
    wa
    #
    cN
    cB
    wne
    cN
    cN
    wne
    wa
    #
    @6
    cA
    cN
    wne
    #
    wa
    #
    wo
    #
    @11
    @7
    @4
    @24
    @5
    @4
    @24
    wi
    @6
    @5
    @1
    @22
    @3
    @23
    @5
    @1
    @22
    cE
    cG
    cN
    cA
    @19
    @19
    eqid
    #
    umgrvad2edg.e
    umgrpredgv
    ex
    @5
    @3
    @23
    cE
    cG
    cB
    cN
    @19
    @29
    umgrvad2edg.e
    umgrpredgv
    ex
    anim12d
    adantr
    imp
    @18
    @27
    @25
    @18
    @6
    @26
    @5
    @6
    @4
    simplr
    @5
    @1
    @26
    @6
    @3
    @5
    @1
    wa
    cN
    cA
    cE
    cG
    cN
    cA
    umgrvad2edg.e
    umgredgne
    necomd
    ad2ant2r
    jca
    olcd
    @24
    @28
    wa
    @8
    @9
    @10
    @24
    @28
    @8
    cN
    cA
    cB
    cN
    @19
    @19
    @19
    @19
    prneimg
    imp
    @20
    @9
    @21
    @23
    @28
    cN
    cA
    @19
    prid1g
    ad3antrrr
    @20
    @10
    @21
    @23
    @28
    cB
    cN
    @19
    prid2g
    ad3antrrr
    3jca
    syl2anc
    @17
    @11
    @0
    @13
    wne
    #
    @9
    @16
    w3a
    vx
    vy
    @0
    @2
    cE
    cE
    @12
    @0
    wceq
    @14
    @30
    @15
    @9
    @16
    @12
    @0
    @13
    neeq1
    @12
    @0
    cN
    eleq2
    3anbi12d
    @13
    @2
    wceq
    @30
    @8
    @16
    @10
    @9
    @13
    @2
    @0
    neeq2
    @13
    @2
    cN
    eleq2
    3anbi13d
    rspc2ev
    syl2an23an
end
