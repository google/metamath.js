include "wfo.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wf.mm"
include "cfv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "dffo3f.mm"
include "simplbi.mm"
include "fmpt.mm"
include "bicomi.mm"
include "biimpi.mm"
include "syl.mm"
include "foelrnf.mm"
include "wi.mm"
include "nfcv.mm"
include "nffo.mm"
include "simpr.mm"
include "r19.21bi.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "reximdai.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpll.mm"
include "rspa.mm"
include "adantll.mm"
include "w3a.mm"
include "simp3.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "3exp.mm"
include "imp.mm"
include "ralrimi.mm"
include "sylibr.mm"
include "impbii.mm"

theorem fompt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fompt.1: |- F = ( x e. A |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint F y
  assert |- ( F : A -onto-> B <-> ( A. x e. A C e. B /\ A. y e. B E. x e. A y = C ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    cC
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    wa
    #
    @0
    @2
    @6
    @0
    cA
    cB
    cF
    wf
    #
    @2
    @0
    @8
    @3
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    vx
    vy
    cA
    cB
    cF
    vx
    cF
    vx
    cA
    cC
    cmpt
    fompt.1
    vx
    cA
    cC
    nfmpt1
    nfcxfr
    #
    dffo3f
    #
    simplbi
    @8
    @2
    @2
    @8
    vx
    cA
    cB
    cC
    cF
    fompt.1
    fmpt
    #
    bicomi
    biimpi
    syl
    #
    @0
    @5
    vy
    cB
    @0
    @3
    cB
    wcel
    #
    wa
    @12
    @5
    vx
    cA
    cB
    @3
    cF
    @14
    foelrnf
    @0
    @12
    @5
    wi
    @18
    @0
    @11
    @4
    vx
    cA
    vx
    cA
    cB
    cF
    @14
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    nffo
    @0
    @9
    cA
    wcel
    #
    @11
    @4
    wi
    @0
    @19
    wa
    #
    @11
    @4
    @20
    @11
    wa
    @3
    @10
    cC
    @20
    @11
    simpr
    @20
    @10
    cC
    wceq
    #
    @11
    @20
    @19
    @1
    @21
    @0
    @19
    simpr
    @0
    @1
    vx
    cA
    @17
    r19.21bi
    vx
    cA
    cC
    cB
    cF
    fompt.1
    fvmpt2
    #
    syl2anc
    adantr
    eqtrd
    ex
    ex
    reximdai
    adantr
    mpd
    ralrimiva
    jca
    @7
    @8
    @13
    wa
    @0
    @7
    @8
    @13
    @2
    @8
    @6
    @2
    @8
    @16
    biimpi
    adantr
    @7
    @12
    vy
    cB
    @2
    @6
    vy
    @2
    vy
    nfv
    @5
    vy
    cB
    nfra1
    nfan
    @7
    @18
    @12
    @7
    @18
    wa
    @2
    @5
    @12
    @2
    @6
    @18
    simpll
    @6
    @18
    @5
    @2
    @5
    vy
    cB
    rspa
    adantll
    @2
    @5
    @12
    @2
    @4
    @11
    vx
    cA
    @1
    vx
    cA
    nfra1
    @2
    @19
    @4
    @11
    @2
    @19
    @4
    w3a
    @3
    cC
    @10
    @2
    @19
    @4
    simp3
    @2
    @19
    cC
    @10
    wceq
    @4
    @2
    @19
    wa
    #
    @10
    cC
    @23
    @19
    @1
    @21
    @2
    @19
    simpr
    @1
    vx
    cA
    rspa
    @22
    syl2anc
    eqcomd
    3adant3
    eqtrd
    3exp
    reximdai
    imp
    syl2anc
    ex
    ralrimi
    jca
    @15
    sylibr
    impbii
end
