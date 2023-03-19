include "cres.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "ccom.mm"
include "climc.mm"
include "cdm.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wral.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "cr.mm"
include "wf.mm"
include "fssresd.mm"
include "fdm.mm"
include "syl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "cc.mm"
include "recnd.mm"
include "sselda.mm"
include "addneintrd.mm"
include "neneqd.mm"
include "wb.mm"
include "readdcld.mm"
include "elsng.mm"
include "mtbird.mm"
include "eldifd.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "constlimc.mm"
include "idlimc.mm"
include "addlimc.mm"
include "limccog.mm"
include "cfv.mm"
include "wrex.mm"
include "simpr.mm"
include "elrnmpt.mm"
include "adantl.mm"
include "mpbid.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcri.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "dfss3.mm"
include "sylibr.mm"
include "cores.mm"
include "fmptd.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "a1i.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "eqidd.mm"
include "fvmptd.mm"
include "mpteq2dva.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "oveq1d.mm"

theorem fourierdlem53
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume fourierdlem53.1: |- ( ph -> F : RR --> RR )
  assume fourierdlem53.2: |- ( ph -> X e. RR )
  assume fourierdlem53.3: |- ( ph -> A C_ RR )
  assume fourierdlem53.g: |- G = ( s e. A |-> ( F ` ( X + s ) ) )
  assume fourierdlem53.xps: |- ( ( ph /\ s e. A ) -> ( X + s ) e. B )
  assume fourierdlem53.b: |- ( ph -> B C_ RR )
  assume fourierdlem53.sned: |- ( ( ph /\ s e. A ) -> s =/= D )
  assume fourierdlem53.c: |- ( ph -> C e. ( ( F |` B ) limCC ( X + D ) ) )
  assume fourierdlem53.d: |- ( ph -> D e. CC )

  disjoint A s
  disjoint B s
  disjoint D s
  disjoint F s
  disjoint X s
  disjoint ph s
  disjoint A x
  disjoint s x
  disjoint A y
  disjoint s y
  disjoint B y
  disjoint F x
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> C e. ( G limCC D ) )

  proof
    wph
    cC
    cF
    cB
    cres
    #
    vs
    cA
    cX
    vs
    cv
    #
    caddc
    co
    #
    cmpt
    #
    ccom
    #
    cD
    climc
    co
    cG
    cD
    climc
    co
    wph
    cD
    cX
    cD
    caddc
    co
    #
    cC
    @3
    @0
    wph
    @2
    @0
    cdm
    #
    @5
    csn
    #
    cdif
    #
    wcel
    #
    vs
    cA
    wral
    @3
    crn
    #
    @8
    wss
    wph
    @9
    vs
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @2
    @6
    @7
    @12
    @2
    cB
    @6
    fourierdlem53.xps
    wph
    cB
    @6
    wceq
    @11
    wph
    @6
    cB
    wph
    cB
    cr
    @0
    wf
    @6
    cB
    wceq
    wph
    cr
    cr
    cB
    cF
    fourierdlem53.1
    fourierdlem53.b
    fssresd
    cB
    cr
    @0
    fdm
    syl
    eqcomd
    adantr
    eleqtrd
    @12
    @2
    @7
    wcel
    #
    @2
    @5
    wceq
    #
    @12
    @2
    @5
    @12
    cX
    @1
    cD
    wph
    cX
    cc
    wcel
    @11
    wph
    cX
    fourierdlem53.2
    recnd
    #
    adantr
    #
    @12
    @1
    wph
    cA
    cr
    @1
    fourierdlem53.3
    sselda
    #
    recnd
    #
    wph
    cD
    cc
    wcel
    @11
    fourierdlem53.d
    adantr
    fourierdlem53.sned
    addneintrd
    neneqd
    @12
    @2
    cr
    wcel
    @13
    @14
    wb
    @12
    cX
    @1
    wph
    cX
    cr
    wcel
    #
    @11
    fourierdlem53.2
    adantr
    @17
    readdcld
    #
    @2
    @5
    cr
    elsng
    syl
    mtbird
    eldifd
    ralrimiva
    vs
    cA
    @2
    @8
    @3
    @3
    eqid
    #
    rnmptss
    syl
    wph
    vs
    cA
    cX
    @1
    cD
    cX
    vs
    cA
    cX
    cmpt
    #
    vs
    cA
    @1
    cmpt
    #
    @3
    cD
    @22
    eqid
    #
    @23
    eqid
    #
    @21
    @16
    @18
    wph
    vs
    cA
    cX
    cD
    @22
    @24
    wph
    cA
    cr
    cc
    fourierdlem53.3
    ax-resscn
    syl6ss
    #
    @15
    fourierdlem53.d
    constlimc
    wph
    vs
    cA
    @23
    cD
    @26
    @25
    fourierdlem53.d
    idlimc
    addlimc
    fourierdlem53.c
    limccog
    wph
    @4
    cG
    cD
    climc
    wph
    @4
    cF
    @3
    ccom
    #
    vx
    cA
    vx
    cv
    #
    @3
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    cG
    wph
    @10
    cB
    wss
    #
    @4
    @27
    wceq
    wph
    vy
    cv
    #
    cB
    wcel
    #
    vy
    @10
    wral
    @32
    wph
    @34
    vy
    @10
    wph
    @33
    @10
    wcel
    #
    wa
    #
    @33
    @2
    wceq
    #
    vs
    cA
    wrex
    #
    @34
    @36
    @35
    @38
    wph
    @35
    simpr
    @35
    @35
    @38
    wb
    wph
    vs
    cA
    @2
    @33
    @3
    @10
    @21
    elrnmpt
    adantl
    mpbid
    @36
    @37
    @34
    vs
    cA
    wph
    @35
    vs
    wph
    vs
    nfv
    vs
    vy
    @10
    vs
    @3
    vs
    cA
    @2
    nfmpt1
    nfrn
    nfcri
    nfan
    @34
    vs
    nfv
    wph
    @11
    @37
    @34
    wi
    wi
    @35
    wph
    @11
    @37
    @34
    wph
    @11
    @37
    w3a
    @33
    @2
    cB
    wph
    @11
    @37
    simp3
    wph
    @11
    @2
    cB
    wcel
    @37
    fourierdlem53.xps
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    ralrimiva
    vy
    @10
    cB
    dfss3
    sylibr
    cF
    @3
    cB
    cores
    syl
    wph
    cr
    cr
    cF
    wf
    cA
    cr
    @3
    wf
    @27
    @31
    wceq
    fourierdlem53.1
    wph
    vs
    cA
    @2
    cr
    @3
    @20
    @21
    fmptd
    vx
    cF
    @3
    cA
    cr
    cr
    fcompt
    syl2anc
    wph
    cG
    vs
    cA
    @2
    cF
    cfv
    #
    cmpt
    #
    vx
    cA
    cX
    @28
    caddc
    co
    #
    cF
    cfv
    #
    cmpt
    #
    @31
    cG
    @40
    wceq
    wph
    fourierdlem53.g
    a1i
    @40
    @43
    wceq
    wph
    vs
    vx
    cA
    @39
    @42
    @1
    @28
    wceq
    #
    @2
    @41
    cF
    @1
    @28
    cX
    caddc
    oveq2
    #
    fveq2d
    cbvmptv
    a1i
    wph
    vx
    cA
    @42
    @30
    wph
    @28
    cA
    wcel
    #
    wa
    #
    @41
    @29
    cF
    @47
    @29
    @41
    @47
    vs
    @28
    @2
    @41
    cA
    @3
    cr
    @47
    @3
    eqidd
    @44
    @2
    @41
    wceq
    @47
    @45
    adantl
    wph
    @46
    simpr
    @47
    cX
    @28
    wph
    @19
    @46
    fourierdlem53.2
    adantr
    wph
    cA
    cr
    @28
    fourierdlem53.3
    sselda
    readdcld
    fvmptd
    eqcomd
    fveq2d
    mpteq2dva
    3eqtrrd
    3eqtrd
    oveq1d
    eleqtrd
end
