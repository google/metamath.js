include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "simpr.mm"
include "fveq1d.mm"
include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "elmapfn.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "fnsng.mm"
include "syl2anc.mm"
include "wn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "snidg.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "adantr.mm"
include "wrex.mm"
include "cmpt.mm"
include "uneq1.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "elrnmpti.mm"
include "sylib.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "invdisj.mm"

theorem actfunsnrndisj
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  assume actfunsn.1: |- ( ( ph /\ k e. C ) -> A C_ ( C ^m B ) )
  assume actfunsn.2: |- ( ph -> C e. _V )
  assume actfunsn.3: |- ( ph -> I e. V )
  assume actfunsn.4: |- ( ph -> -. I e. B )
  assume actfunsn.5: |- F = ( x e. A |-> ( x u. { <. I , k >. } ) )

  disjoint A x
  disjoint I k
  disjoint I x
  disjoint k x
  disjoint k ph
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C f
  disjoint C y
  disjoint C z
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint F y
  disjoint F z
  disjoint I y
  disjoint I z
  disjoint k y
  disjoint k z
  disjoint f k
  disjoint f x
  disjoint f ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> Disj_ k e. C ran F )

  proof
    wph
    cI
    vf
    cv
    #
    cfv
    #
    vk
    cv
    #
    wceq
    #
    vf
    cF
    crn
    #
    wral
    #
    vk
    cC
    wral
    vk
    cC
    @4
    wdisj
    wph
    @5
    vk
    cC
    wph
    @2
    cC
    wcel
    #
    wa
    #
    @3
    vf
    @4
    @7
    @0
    @4
    wcel
    #
    wa
    #
    @0
    vz
    cv
    #
    cI
    @2
    cop
    #
    csn
    #
    cun
    #
    wceq
    #
    @3
    vz
    cA
    @9
    @10
    cA
    wcel
    #
    wa
    #
    @14
    wa
    #
    @1
    cI
    @13
    cfv
    #
    @2
    @17
    cI
    @0
    @13
    @16
    @14
    simpr
    fveq1d
    @16
    @18
    @2
    wceq
    @14
    @16
    @18
    cI
    @12
    cfv
    #
    @2
    @16
    @10
    cB
    wfn
    #
    @12
    cI
    csn
    #
    wfn
    #
    cB
    @21
    cin
    c0
    wceq
    #
    cI
    @21
    wcel
    #
    @18
    @19
    wceq
    @16
    @10
    cC
    cB
    cmap
    co
    #
    wcel
    @20
    @16
    cA
    @25
    @10
    @7
    cA
    @25
    wss
    @8
    @15
    actfunsn.1
    ad2antrr
    @9
    @15
    simpr
    sseldd
    @10
    cC
    cB
    elmapfn
    syl
    @16
    cI
    cV
    wcel
    #
    @6
    @22
    wph
    @26
    @6
    @8
    @15
    actfunsn.3
    ad3antrrr
    #
    wph
    @6
    @8
    @15
    simpllr
    #
    cI
    @2
    cV
    cC
    fnsng
    syl2anc
    wph
    @23
    @6
    @8
    @15
    wph
    cI
    cB
    wcel
    wn
    @23
    actfunsn.4
    cB
    cI
    disjsn
    sylibr
    ad3antrrr
    @16
    @26
    @24
    @27
    cI
    cV
    snidg
    syl
    cB
    @21
    @10
    @12
    cI
    fvun2
    syl112anc
    @16
    @26
    @6
    @19
    @2
    wceq
    @27
    @28
    cI
    @2
    cV
    cC
    fvsng
    syl2anc
    eqtrd
    adantr
    eqtrd
    @9
    @8
    @14
    vz
    cA
    wrex
    @7
    @8
    simpr
    vz
    cA
    @13
    @0
    cF
    cF
    vx
    cA
    vx
    cv
    #
    @12
    cun
    #
    cmpt
    vz
    cA
    @13
    cmpt
    actfunsn.5
    vx
    vz
    cA
    @30
    @13
    @29
    @10
    @12
    uneq1
    cbvmptv
    eqtri
    @10
    @12
    vz
    vex
    @11
    snex
    unex
    elrnmpti
    sylib
    r19.29a
    ralrimiva
    ralrimiva
    vk
    vf
    cC
    @4
    @1
    invdisj
    syl
end
