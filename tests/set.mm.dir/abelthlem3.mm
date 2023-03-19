include "wcel.mm"
include "c1.mm"
include "csn.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wo.mm"
include "caddc.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wa.mm"
include "cun.mm"
include "cdif.mm"
include "wss.mm"
include "abelthlem2.mm"
include "simprd.mm"
include "ssundif.mm"
include "sylibr.mm"
include "sselda.mm"
include "elun.mm"
include "sylib.mm"
include "cc.mm"
include "feqmptd.mm"
include "ffvelrnda.mm"
include "mulid1d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "elsni.mm"
include "oveq1d.mm"
include "cz.mm"
include "wceq.mm"
include "nn0z.mm"
include "1exp.mm"
include "syl.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "eqcomd.mm"
include "seqeq3d.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "0cn.mm"
include "1re.mm"
include "rexri.mm"
include "blssm.mm"
include "mp3an.mm"
include "simpr.mm"
include "sseldi.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "cr.mm"
include "crab.mm"
include "clt.mm"
include "csup.mm"
include "wf.mm"
include "abscld.mm"
include "rexrd.mm"
include "rexr.mm"
include "mp1i.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "cnmetdval.mm"
include "sylancl.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "wbr.mm"
include "wb.mm"
include "elbl3.mm"
include "mpanl12.mm"
include "sylancr.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "cle.mm"
include "abelthlem1.mm"
include "xrltletrd.mm"
include "radcnvlt2.mm"
include "jaodan.mm"
include "syldan.mm"

theorem abelthlem3
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cM: class M
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vr: setvar r
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  let cF: class F
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }

  disjoint n z
  disjoint M n
  disjoint M z
  disjoint X n
  disjoint X z
  disjoint A n
  disjoint A z
  disjoint n ph
  disjoint S n
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint M k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint n r
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint X x
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
  disjoint A k
  disjoint m r
  disjoint m t
  disjoint m v
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S r
  disjoint S w
  disjoint S x
  disjoint S y
  assert |- ( ( ph /\ X e. S ) -> seq 0 ( + , ( n e. NN0 |-> ( ( A ` n ) x. ( X ^ n ) ) ) ) e. dom ~~> )

  proof
    wph
    cX
    cS
    wcel
    #
    cX
    c1
    csn
    #
    wcel
    #
    cX
    cc0
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    wcel
    #
    wo
    #
    caddc
    vn
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    cX
    @7
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    wph
    @0
    wa
    cX
    @1
    @4
    cun
    #
    wcel
    @6
    wph
    cS
    @15
    cX
    wph
    cS
    @1
    cdif
    @4
    wss
    #
    cS
    @15
    wss
    wph
    c1
    cS
    wcel
    @16
    wph
    vz
    cA
    cS
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelthlem2
    simprd
    cS
    @1
    @4
    ssundif
    sylibr
    sselda
    cX
    @1
    @4
    elun
    sylib
    wph
    @2
    @14
    @5
    wph
    @2
    wa
    #
    caddc
    cA
    cc0
    cseq
    #
    @12
    @13
    @17
    cA
    @11
    caddc
    cc0
    wph
    @2
    cA
    vn
    cn0
    @8
    c1
    cmul
    co
    #
    cmpt
    #
    @11
    wph
    cA
    vn
    cn0
    @8
    cmpt
    @20
    wph
    vn
    cn0
    cc
    cA
    abelth.1
    feqmptd
    wph
    vn
    cn0
    @19
    @8
    wph
    @7
    cn0
    wcel
    #
    wa
    @8
    wph
    cn0
    cc
    @7
    cA
    abelth.1
    ffvelrnda
    mulid1d
    mpteq2dva
    eqtr4d
    @2
    @11
    @20
    @2
    vn
    cn0
    @10
    @19
    @2
    @21
    wa
    @9
    c1
    @8
    cmul
    @2
    @21
    @9
    c1
    @7
    cexp
    co
    #
    c1
    @2
    cX
    c1
    @7
    cexp
    cX
    c1
    elsni
    oveq1d
    @21
    @7
    cz
    wcel
    @22
    c1
    wceq
    @7
    nn0z
    @7
    1exp
    syl
    sylan9eq
    oveq2d
    mpteq2dva
    eqcomd
    sylan9eq
    seqeq3d
    wph
    @18
    @13
    wcel
    @2
    abelth.2
    adantr
    eqeltrrd
    wph
    @5
    wa
    #
    caddc
    cX
    vz
    cc
    vn
    cn0
    @8
    vz
    cv
    #
    @7
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cc0
    cseq
    @12
    @13
    @23
    @29
    @11
    caddc
    cc0
    @23
    cX
    cc
    wcel
    #
    @29
    @11
    wceq
    @23
    @4
    cc
    cX
    @3
    cc
    cxmt
    cfv
    wcel
    #
    cc0
    cc
    wcel
    #
    c1
    cxr
    wcel
    #
    @4
    cc
    wss
    cnxmet
    0cn
    c1
    1re
    rexri
    #
    @3
    cc0
    c1
    cc
    blssm
    mp3an
    wph
    @5
    simpr
    #
    sseldi
    #
    vz
    cX
    @27
    @11
    cc
    @28
    @24
    cX
    wceq
    #
    vn
    cn0
    @26
    @10
    @37
    @25
    @9
    @8
    cmul
    @24
    cX
    @7
    cexp
    oveq1
    oveq2d
    mpteq2dv
    @28
    eqid
    #
    vn
    cn0
    @10
    nn0ex
    mptex
    fvmpt
    syl
    seqeq3d
    @23
    vz
    cA
    caddc
    vr
    cv
    @28
    cfv
    cc0
    cseq
    @13
    wcel
    vr
    cr
    crab
    cxr
    clt
    csup
    #
    vn
    @28
    cX
    vr
    @38
    wph
    cn0
    cc
    cA
    wf
    @5
    abelth.1
    adantr
    #
    @39
    eqid
    #
    @36
    @23
    cX
    cabs
    cfv
    #
    c1
    @39
    @23
    @42
    @23
    cX
    @36
    abscld
    rexrd
    c1
    cr
    wcel
    @33
    @23
    1re
    c1
    rexr
    mp1i
    @23
    cc0
    cpnf
    cicc
    co
    cxr
    @39
    cc0
    cpnf
    iccssxr
    @23
    vz
    cA
    @39
    vn
    @28
    vr
    @38
    @40
    @41
    radcnvcl
    sseldi
    @23
    cX
    cc0
    @3
    co
    #
    @42
    c1
    clt
    @23
    @43
    cX
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @42
    @23
    @30
    @32
    @43
    @45
    wceq
    @36
    0cn
    cX
    cc0
    @3
    @3
    eqid
    cnmetdval
    sylancl
    @23
    @44
    cX
    cabs
    @23
    cX
    @36
    subid1d
    fveq2d
    eqtrd
    @23
    @5
    @43
    c1
    clt
    wbr
    #
    @35
    @23
    @32
    @30
    @5
    @46
    wb
    #
    0cn
    @36
    @31
    @33
    @32
    @30
    wa
    @47
    cnxmet
    @34
    cX
    @3
    cc0
    c1
    cc
    elbl3
    mpanl12
    sylancr
    mpbid
    eqbrtrrd
    wph
    c1
    @39
    cle
    wbr
    @5
    wph
    vz
    cA
    vn
    vr
    abelth.1
    abelth.2
    abelthlem1
    adantr
    xrltletrd
    radcnvlt2
    eqeltrrd
    jaodan
    syldan
end
