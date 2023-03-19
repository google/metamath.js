include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "uneq1.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "a1i.mm"
include "resex.mm"
include "wceq.mm"
include "wrex.mm"
include "rspe.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "adantll.mm"
include "simpr.mm"
include "reseq1d.mm"
include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "cmap.mm"
include "co.mm"
include "sselda.mm"
include "elmapfn.mm"
include "syl.mm"
include "fnsng.mm"
include "sylan.mm"
include "adantr.mm"
include "wn.mm"
include "disjsn.mm"
include "fnunres1.mm"
include "syl3anc.mm"
include "eqtr2d.mm"
include "jca.mm"
include "anasss.mm"
include "wss.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "sseldd.mm"
include "ad4antr.mm"
include "simp-4r.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "sylib.mm"
include "r19.29a.mm"
include "uneq1d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "impbida.mm"
include "f1od.mm"

theorem actfunsnf1o
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
  assert |- ( ( ph /\ k e. C ) -> F : A -1-1-onto-> ran F )

  proof
    wph
    vk
    cv
    #
    cC
    wcel
    #
    wa
    #
    vz
    vy
    cA
    cF
    crn
    #
    vz
    cv
    #
    cI
    @0
    cop
    #
    csn
    #
    cun
    #
    vy
    cv
    #
    cB
    cres
    #
    cF
    cvv
    cvv
    cF
    vx
    cA
    vx
    cv
    #
    @6
    cun
    #
    cmpt
    vz
    cA
    @7
    cmpt
    actfunsn.5
    vx
    vz
    cA
    @11
    @7
    @10
    @4
    @6
    uneq1
    cbvmptv
    eqtri
    #
    @7
    cvv
    wcel
    @2
    @4
    cA
    wcel
    #
    wa
    #
    @4
    @6
    vz
    vex
    @5
    snex
    unex
    #
    a1i
    @9
    cvv
    wcel
    @2
    @8
    @3
    wcel
    #
    wa
    #
    @8
    cB
    vy
    vex
    resex
    a1i
    @2
    @13
    @8
    @7
    wceq
    #
    wa
    #
    @16
    @4
    @9
    wceq
    #
    wa
    #
    @2
    @13
    @18
    @21
    @14
    @18
    wa
    #
    @16
    @20
    @13
    @18
    @16
    @2
    @19
    @18
    vz
    cA
    wrex
    #
    @16
    @18
    vz
    cA
    rspe
    vz
    cA
    @7
    @8
    cF
    @12
    @15
    elrnmpti
    #
    sylibr
    adantll
    @22
    @9
    @7
    cB
    cres
    #
    @4
    @22
    @8
    @7
    cB
    @14
    @18
    simpr
    reseq1d
    @14
    @25
    @4
    wceq
    #
    @18
    @14
    @4
    cB
    wfn
    #
    @6
    cI
    csn
    #
    wfn
    #
    cB
    @28
    cin
    c0
    wceq
    #
    @26
    @14
    @4
    cC
    cB
    cmap
    co
    #
    wcel
    #
    @27
    @2
    cA
    @31
    @4
    actfunsn.1
    sselda
    @4
    cC
    cB
    elmapfn
    #
    syl
    @2
    @29
    @13
    wph
    cI
    cV
    wcel
    #
    @1
    @29
    actfunsn.3
    cI
    @0
    cV
    cC
    fnsng
    #
    sylan
    adantr
    @2
    @30
    @13
    wph
    @30
    @1
    wph
    cI
    cB
    wcel
    wn
    @30
    actfunsn.4
    cB
    cI
    disjsn
    sylibr
    #
    adantr
    adantr
    cB
    @28
    @4
    @6
    fnunres1
    #
    syl3anc
    adantr
    eqtr2d
    jca
    anasss
    @2
    @16
    @20
    @19
    @17
    @20
    wa
    #
    @13
    @18
    @38
    @4
    @9
    cA
    @17
    @20
    simpr
    #
    @17
    @9
    cA
    wcel
    #
    @20
    @17
    @18
    @40
    vz
    cA
    @17
    @13
    wa
    #
    @18
    wa
    #
    @9
    @25
    cA
    @42
    @8
    @7
    cB
    @41
    @18
    simpr
    #
    reseq1d
    #
    @42
    @25
    @4
    cA
    @42
    @27
    @29
    @30
    @26
    @42
    @32
    @27
    @42
    cA
    @31
    @4
    @2
    cA
    @31
    wss
    @16
    @13
    @18
    actfunsn.1
    ad3antrrr
    @17
    @13
    @18
    simplr
    #
    sseldd
    @33
    syl
    @42
    @34
    @1
    @29
    wph
    @34
    @1
    @16
    @13
    @18
    actfunsn.3
    ad4antr
    wph
    @1
    @16
    @13
    @18
    simp-4r
    @35
    syl2anc
    wph
    @30
    @1
    @16
    @13
    @18
    @36
    ad4antr
    @37
    syl3anc
    #
    @45
    eqeltrd
    eqeltrd
    @17
    @16
    @23
    @2
    @16
    simpr
    @24
    sylib
    #
    r19.29a
    adantr
    eqeltrd
    @38
    @7
    @9
    @6
    cun
    #
    @8
    @38
    @4
    @9
    @6
    @39
    uneq1d
    @17
    @48
    @8
    wceq
    #
    @20
    @17
    @18
    @49
    vz
    cA
    @42
    @48
    @7
    @8
    @42
    @9
    @4
    @6
    @42
    @9
    @25
    @4
    @44
    @46
    eqtrd
    uneq1d
    @43
    eqtr4d
    @47
    r19.29a
    adantr
    eqtr2d
    jca
    anasss
    impbida
    f1od
end
