include "csu.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "eqid.mm"
include "cv.mm"
include "wa.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "cc.mm"
include "ctopon.mm"
include "wss.mm"
include "wb.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "wf.mm"
include "adantr.mm"
include "retopon.mm"
include "eqeltri.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "frn.mm"
include "syl.mm"
include "ax-resscn.mm"
include "cnrest2.mm"
include "mpbird.mm"
include "fsumcnf.mm"
include "wceq.mm"
include "wrex.mm"
include "wfn.mm"
include "wral.mm"
include "cfn.mm"
include "simpll.mm"
include "simpr.mm"
include "jca.mm"
include "simplr.mm"
include "wi.mm"
include "fmpt.mm"
include "sylibr.mm"
include "rsp.mm"
include "sylc.mm"
include "fsumrecl.mm"
include "ex.mm"
include "ralrimi.mm"
include "fnmpt.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "fvelrnbf.mm"
include "biimpa.mm"
include "nfrn.mm"
include "nfcri.mm"
include "nfan.mm"
include "w3a.mm"
include "fvmpt2.mm"
include "3adant3.mm"
include "simp3.mm"
include "eqtr3d.mm"
include "eqeltrrd.mm"
include "3adant1r.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ssrdv.mm"
include "mpbid.mm"
include "syl6eleqr.mm"

theorem refsumcn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  assume refsumcn.1: |- F/ x ph
  assume refsumcn.2: |- K = ( topGen ` ran (,) )
  assume refsumcn.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume refsumcn.4: |- ( ph -> A e. Fin )
  assume refsumcn.5: |- ( ( ph /\ k e. A ) -> ( x e. X |-> B ) e. ( J Cn K ) )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint J k
  disjoint J x
  disjoint X k
  disjoint X x
  disjoint k ph
  disjoint k y
  disjoint x y
  disjoint A y
  disjoint X y
  disjoint ph y
  disjoint B y
  assert |- ( ph -> ( x e. X |-> sum_ k e. A B ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    cA
    cB
    vk
    csu
    #
    cmpt
    #
    cJ
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    #
    wph
    @1
    cJ
    @2
    ccn
    co
    #
    wcel
    #
    @1
    @4
    wcel
    #
    wph
    vx
    cA
    cB
    vk
    cJ
    @2
    cX
    @2
    eqid
    #
    refsumcn.3
    refsumcn.4
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    #
    vx
    cX
    cB
    cmpt
    #
    @6
    wcel
    #
    @12
    @4
    wcel
    #
    @11
    @12
    @5
    @4
    refsumcn.5
    cK
    @3
    cJ
    ccn
    cK
    cioo
    crn
    ctg
    cfv
    #
    @3
    refsumcn.2
    @2
    @9
    tgioo2
    eqtri
    oveq2i
    #
    syl6eleq
    @11
    @2
    cc
    ctopon
    cfv
    wcel
    #
    @12
    crn
    cr
    wss
    #
    cr
    cc
    wss
    #
    @13
    @14
    wb
    @17
    @11
    @2
    @9
    cnfldtopon
    #
    a1i
    @11
    cX
    cr
    @12
    wf
    #
    @18
    @11
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cr
    ctopon
    cfv
    #
    wcel
    #
    @12
    @5
    wcel
    @21
    wph
    @22
    @10
    refsumcn.3
    adantr
    @24
    @11
    cK
    @15
    @23
    refsumcn.2
    retopon
    eqeltri
    a1i
    refsumcn.5
    @12
    cJ
    cK
    cX
    cr
    cnf2
    syl3anc
    #
    cX
    cr
    @12
    frn
    syl
    @19
    @11
    ax-resscn
    a1i
    cr
    @12
    cJ
    @2
    cc
    cnrest2
    syl3anc
    mpbird
    fsumcnf
    wph
    @17
    @1
    crn
    #
    cr
    wss
    @19
    @7
    @8
    wb
    @17
    wph
    @20
    a1i
    wph
    vy
    @26
    cr
    wph
    vy
    cv
    #
    @26
    wcel
    #
    @27
    cr
    wcel
    #
    wph
    @28
    wa
    #
    vx
    cv
    #
    @1
    cfv
    #
    @27
    wceq
    #
    vx
    cX
    wrex
    #
    @29
    wph
    @28
    @34
    wph
    @1
    cX
    wfn
    #
    @28
    @34
    wb
    wph
    @0
    cr
    wcel
    #
    vx
    cX
    wral
    @35
    wph
    @36
    vx
    cX
    refsumcn.1
    wph
    @31
    cX
    wcel
    #
    @36
    wph
    @37
    wa
    #
    cA
    cB
    vk
    wph
    cA
    cfn
    wcel
    @37
    refsumcn.4
    adantr
    @38
    @10
    wa
    #
    @11
    @37
    cB
    cr
    wcel
    #
    @39
    wph
    @10
    wph
    @37
    @10
    simpll
    @38
    @10
    simpr
    jca
    wph
    @37
    @10
    simplr
    @11
    @40
    vx
    cX
    wral
    #
    @37
    @40
    wi
    @11
    @21
    @41
    @25
    vx
    cX
    cr
    cB
    @12
    @12
    eqid
    fmpt
    sylibr
    @40
    vx
    cX
    rsp
    syl
    sylc
    fsumrecl
    #
    ex
    ralrimi
    vx
    cX
    @0
    @1
    cr
    @1
    eqid
    #
    fnmpt
    syl
    vx
    cX
    @27
    @1
    vx
    cX
    nfcv
    vx
    @27
    nfcv
    vx
    cX
    @0
    nfmpt1
    #
    fvelrnbf
    syl
    biimpa
    @30
    @33
    @29
    vx
    cX
    wph
    @28
    vx
    refsumcn.1
    vx
    vy
    @26
    vx
    @1
    @44
    nfrn
    nfcri
    nfan
    vx
    vy
    cr
    vx
    cr
    nfcv
    nfcri
    @30
    @37
    @33
    @29
    wph
    @37
    @33
    @29
    @28
    wph
    @37
    @33
    w3a
    #
    @0
    @27
    cr
    @45
    @32
    @0
    @27
    wph
    @37
    @32
    @0
    wceq
    #
    @33
    @38
    @37
    @36
    wa
    @46
    @38
    @37
    @36
    wph
    @37
    simpr
    @42
    jca
    vx
    cX
    @0
    cr
    @1
    @43
    fvmpt2
    syl
    3adant3
    wph
    @37
    @33
    simp3
    eqtr3d
    wph
    @37
    @36
    @33
    @42
    3adant3
    eqeltrrd
    3adant1r
    3exp
    rexlimd
    mpd
    ex
    ssrdv
    @19
    wph
    ax-resscn
    a1i
    cr
    @1
    cJ
    @2
    cc
    cnrest2
    syl3anc
    mpbid
    @16
    syl6eleqr
end
