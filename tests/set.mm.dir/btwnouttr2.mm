include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "ccgr.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simp3r.mm"
include "axsegcon.mm"
include "syl122anc.mm"
include "adantr.mm"
include "wi.mm"
include "simprrl.mm"
include "wceq.mm"
include "simprl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "jca.mm"
include "adantl.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3l.mm"
include "simpr.mm"
include "btwnexch3.mm"
include "mpd.mm"
include "simprrr.mm"
include "simprl3.mm"
include "simpl3r.mm"
include "cgrrflxd.mm"
include "segconeq.mm"
include "syl133anc.mm"
include "mp3and.mm"
include "opeq2d.mm"
include "breqtrd.mm"
include "expr.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "ex.mm"

theorem btwnouttr2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B =/= C /\ B Btwn <. A , C >. /\ C Btwn <. B , D >. ) -> C Btwn <. A , D >. ) )

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
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cB
    cC
    wne
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cC
    cB
    cD
    cop
    cbtwn
    wbr
    #
    w3a
    #
    cC
    cA
    cD
    cop
    #
    cbtwn
    wbr
    #
    @8
    @12
    wa
    #
    cC
    cA
    vx
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    cC
    @16
    cop
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    @14
    @8
    @22
    @12
    @8
    @0
    @2
    @5
    @5
    @6
    @22
    @0
    @4
    @7
    simp1
    @0
    @2
    @3
    @7
    simp2l
    @0
    @4
    @5
    @6
    simp3l
    #
    @23
    @0
    @4
    @5
    @6
    simp3r
    vx
    cA
    cC
    cC
    cD
    cN
    axsegcon
    syl122anc
    adantr
    @15
    @21
    @14
    vx
    @1
    @8
    @16
    @1
    wcel
    #
    @12
    @21
    @14
    wi
    @8
    @24
    wa
    #
    @12
    @21
    @14
    @25
    @12
    @21
    wa
    #
    wa
    #
    cC
    @17
    @13
    cbtwn
    @25
    @12
    @18
    @20
    simprrl
    @27
    @16
    cD
    cA
    @27
    @9
    cC
    cB
    @16
    cop
    cbtwn
    wbr
    #
    @20
    wa
    #
    @11
    @19
    @19
    ccgr
    wbr
    #
    wa
    #
    @16
    cD
    wceq
    #
    @9
    @10
    @11
    @21
    @25
    simprl1
    @27
    @28
    @20
    @27
    @10
    @18
    wa
    #
    @28
    @26
    @33
    @25
    @26
    @10
    @18
    @9
    @10
    @11
    @21
    simpl2
    @12
    @18
    @20
    simprl
    jca
    adantl
    @25
    @33
    @28
    wi
    #
    @26
    @25
    @0
    @2
    @3
    @5
    @24
    @34
    @0
    @4
    @7
    @24
    simpl1
    #
    @2
    @3
    @0
    @7
    @24
    simpl2l
    @2
    @3
    @0
    @7
    @24
    simpl2r
    #
    @5
    @6
    @0
    @4
    @24
    simpl3l
    #
    @8
    @24
    simpr
    #
    cA
    cB
    cC
    @16
    cN
    btwnexch3
    syl122anc
    adantr
    mpd
    @25
    @12
    @18
    @20
    simprrr
    jca
    @27
    @11
    @30
    @9
    @10
    @11
    @21
    @25
    simprl3
    @25
    @30
    @26
    @25
    cC
    cD
    cN
    @35
    @37
    @5
    @6
    @0
    @4
    @24
    simpl3r
    #
    cgrrflxd
    adantr
    jca
    @25
    @9
    @29
    @31
    w3a
    @32
    wi
    #
    @26
    @25
    @0
    @5
    @5
    @6
    @3
    @24
    @6
    @40
    @35
    @37
    @37
    @39
    @36
    @38
    @39
    cC
    cC
    cD
    cB
    cN
    @16
    cD
    segconeq
    syl133anc
    adantr
    mp3and
    opeq2d
    breqtrd
    expr
    an32s
    rexlimdva
    mpd
    ex
end
