include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "clsp.mm"
include "cuz.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cinf.mm"
include "cr.mm"
include "cvv.mm"
include "nfv.mm"
include "eluzelz2d.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "limsupequzmpt.mm"
include "cdm.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "uzssd2.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "smff.mm"
include "smflimsuplem1.mm"
include "ciin.mm"
include "simpr.mm"
include "wceq.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "eliind.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "limsupvaluzmpt.mm"
include "eqtrd.mm"
include "wss.mm"
include "a1i.mm"
include "fvex.mm"
include "mptex.mm"
include "fvmpt2d.mm"
include "xrltso.mm"
include "supex.mm"
include "dmmpti.mm"
include "iineq2d.mm"
include "eleqtrd.mm"
include "eliinid.mm"
include "syl2anc.mm"
include "mpdan.mm"
include "crab.mm"
include "eluzelz2.mm"
include "uzn0d.mm"
include "wral.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "adantl.mm"
include "rabexd.mm"
include "fvmpt2.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "eqeltrd.mm"
include "cli.mm"
include "mpteq2da.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "eluzelz.mm"
include "peano2zd.mm"
include "zred.mm"
include "ltp1d.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "ltled.mm"
include "eluzd.mm"
include "uzss.mm"
include "syl.mm"
include "rnmptss2.mm"
include "3adant1.mm"
include "simpll.mm"
include "syldanl.mm"
include "uztrn2.mm"
include "adantll.mm"
include "rnmptssd.mm"
include "ressxr.mm"
include "sstrd.mm"
include "3adant3.mm"
include "supxrss.mm"
include "fvexi.mm"
include "ssdf.mm"
include "eqidd.mm"
include "climeldmeqmpt.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "climinf2mpt.mm"
include "eqbrtrd.mm"
include "climreclmpt.mm"

theorem smflimsuplem4
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  assume smflimsuplem4.1: |- F/ n ph
  assume smflimsuplem4.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem4.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem4.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem4.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem4.e: |- E = ( n e. Z |-> { x e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem4.h: |- H = ( n e. Z |-> ( x e. ( E ` n ) |-> sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )
  assume smflimsuplem4.n: |- ( ph -> N e. Z )
  assume smflimsuplem4.i: |- ( ph -> x e. |^|_ n e. ( ZZ>= ` N ) dom ( H ` n ) )
  assume smflimsuplem4.c: |- ( ph -> ( n e. Z |-> ( ( H ` n ) ` x ) ) e. dom ~~> )

  disjoint E n
  disjoint E x
  disjoint n x
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint m n
  disjoint m x
  disjoint H n
  disjoint M m
  disjoint N m
  disjoint N n
  disjoint Z m
  disjoint Z n
  disjoint m ph
  disjoint F k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint N k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( limsup ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) e. RR )

  proof
    wph
    vm
    cZ
    vx
    cv
    #
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    clsp
    cfv
    #
    vn
    cN
    cuz
    cfv
    #
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @3
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    cxr
    clt
    cinf
    #
    cr
    wph
    @4
    vm
    @5
    @3
    cmpt
    clsp
    cfv
    @12
    wph
    cZ
    @5
    @3
    vm
    cM
    cN
    cvv
    cvv
    wph
    vm
    nfv
    #
    smflimsuplem4.m
    wph
    cM
    cN
    cZ
    smflimsuplem4.z
    smflimsuplem4.n
    eluzelz2d
    #
    smflimsuplem4.z
    @5
    eqid
    #
    wph
    @1
    cZ
    wcel
    #
    wa
    @0
    @2
    fvexd
    wph
    @1
    @5
    wcel
    #
    wa
    #
    @0
    @2
    fvexd
    limsupequzmpt
    wph
    @3
    vm
    vn
    cN
    @5
    @13
    @14
    @15
    @18
    @3
    @18
    @2
    cdm
    #
    cr
    @0
    @2
    @18
    @19
    cS
    @2
    wph
    cS
    csalg
    wcel
    @17
    smflimsuplem4.s
    adantr
    wph
    @17
    @16
    @2
    cS
    csmblfn
    cfv
    #
    wcel
    wph
    @5
    cZ
    @1
    wph
    cM
    cN
    cZ
    smflimsuplem4.z
    smflimsuplem4.n
    uzssd2
    #
    sselda
    #
    wph
    cZ
    @20
    @1
    cF
    smflimsuplem4.f
    ffvelrnda
    syldan
    @19
    eqid
    smff
    @18
    @1
    cH
    cfv
    #
    cdm
    #
    @19
    @0
    @18
    vx
    vm
    vn
    cE
    cF
    cH
    @1
    cM
    cZ
    smflimsuplem4.z
    smflimsuplem4.e
    smflimsuplem4.h
    @22
    smflimsuplem1
    @18
    vn
    @0
    @5
    @6
    cH
    cfv
    #
    cdm
    #
    @24
    @1
    wph
    @0
    vn
    @5
    @26
    ciin
    #
    wcel
    @17
    smflimsuplem4.i
    adantr
    wph
    @17
    simpr
    @6
    @1
    wceq
    #
    @26
    @24
    @0
    @28
    @25
    @23
    @6
    @1
    cH
    fveq2
    dmeqd
    eleq2d
    eliind
    sseldd
    ffvelrnd
    #
    rexrd
    limsupvaluzmpt
    eqtrd
    wph
    @0
    @25
    cfv
    #
    @12
    vn
    cN
    @5
    smflimsuplem4.1
    @14
    @15
    wph
    @6
    @5
    wcel
    #
    wa
    #
    @30
    @10
    cr
    @32
    @0
    @6
    cE
    cfv
    #
    wcel
    #
    @30
    @10
    wceq
    @32
    @0
    vn
    @5
    @33
    ciin
    #
    wcel
    #
    @31
    @34
    wph
    @36
    @31
    wph
    @0
    @27
    @35
    smflimsuplem4.i
    wph
    vn
    @5
    @26
    @33
    smflimsuplem4.1
    @32
    @26
    vx
    @33
    @10
    cmpt
    #
    cdm
    #
    @33
    @32
    @25
    @37
    wph
    @31
    @6
    cZ
    wcel
    #
    @25
    @37
    wceq
    @32
    @5
    cZ
    @6
    wph
    @5
    cZ
    wss
    @31
    @21
    adantr
    wph
    @31
    simpr
    #
    sseldd
    #
    wph
    vn
    cZ
    @37
    cH
    cvv
    cH
    vn
    cZ
    @37
    cmpt
    wceq
    wph
    smflimsuplem4.h
    a1i
    @37
    cvv
    wcel
    wph
    @39
    wa
    #
    vx
    @33
    @10
    @6
    cE
    fvex
    mptex
    a1i
    fvmpt2d
    syldan
    #
    dmeqd
    @38
    @33
    wceq
    @32
    vx
    @33
    @10
    @37
    cxr
    @9
    clt
    xrltso
    supex
    #
    @37
    eqid
    dmmpti
    a1i
    eqtrd
    iineq2d
    eleqtrd
    adantr
    @40
    vn
    @0
    @5
    @33
    eliinid
    syl2anc
    #
    @32
    vx
    @33
    @10
    @25
    cvv
    @43
    @10
    cvv
    wcel
    @32
    @34
    wa
    @44
    a1i
    fvmpt2d
    mpdan
    #
    @32
    @0
    vm
    @7
    @19
    ciin
    #
    wcel
    #
    @10
    cr
    wcel
    #
    @32
    @0
    @49
    vx
    @47
    crab
    #
    wcel
    @48
    @49
    wa
    @32
    @0
    @33
    @50
    @45
    @32
    @39
    @50
    cvv
    wcel
    #
    @33
    @50
    wceq
    @41
    wph
    @31
    @39
    @51
    @41
    @42
    @49
    vx
    @47
    @50
    cvv
    @50
    eqid
    @39
    @47
    cvv
    wcel
    wph
    @39
    vm
    @7
    @19
    cvv
    @39
    @6
    @7
    cM
    @6
    cZ
    smflimsuplem4.z
    eluzelz2
    @7
    eqid
    #
    uzn0d
    @19
    cvv
    wcel
    #
    vm
    @7
    wral
    @39
    @53
    vm
    @7
    @2
    @1
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    adantl
    rabexd
    syldan
    vn
    cZ
    @50
    cvv
    cE
    smflimsuplem4.e
    fvmpt2
    syl2anc
    eleqtrd
    @49
    vx
    @47
    rabid
    sylib
    simprd
    #
    eqeltrd
    wph
    vn
    @5
    @30
    cmpt
    #
    @11
    @12
    cli
    wph
    vn
    @5
    @30
    @10
    smflimsuplem4.1
    @46
    mpteq2da
    #
    wph
    @10
    vm
    vk
    cv
    #
    cuz
    cfv
    #
    @3
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    vk
    vn
    cN
    @5
    smflimsuplem4.1
    wph
    vk
    nfv
    @14
    @15
    @54
    @6
    @57
    wceq
    #
    cxr
    @9
    @60
    clt
    @62
    @8
    @59
    @62
    vm
    @7
    @58
    @3
    @6
    @57
    cuz
    fveq2
    mpteq1d
    rneqd
    supeq1d
    wph
    @31
    @57
    @6
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    @60
    @9
    wss
    #
    @9
    cxr
    wss
    #
    @61
    @10
    cle
    wbr
    @31
    @64
    @65
    wph
    @31
    @64
    wa
    #
    vm
    @58
    @7
    @3
    cvv
    @67
    vm
    nfv
    @67
    @57
    @7
    wcel
    @58
    @7
    wss
    @67
    @6
    @57
    @7
    @52
    @31
    @6
    cz
    wcel
    @64
    cN
    @6
    eluzelz
    adantr
    #
    @67
    @57
    @63
    cz
    @31
    @64
    simpr
    #
    @67
    @6
    @68
    peano2zd
    eqeltrd
    #
    @67
    @6
    @57
    @67
    @6
    @68
    zred
    #
    @67
    @57
    @70
    zred
    @67
    @6
    @63
    @57
    clt
    @67
    @6
    @71
    ltp1d
    @67
    @57
    @63
    @69
    eqcomd
    breqtrd
    ltled
    eluzd
    @6
    @57
    uzss
    syl
    @67
    @1
    @58
    wcel
    wa
    @0
    @2
    fvexd
    rnmptss2
    3adant1
    wph
    @31
    @66
    @64
    @32
    @9
    cr
    cxr
    @32
    vm
    @7
    @3
    cr
    @8
    @32
    vm
    nfv
    @8
    eqid
    @32
    @1
    @7
    wcel
    #
    wa
    wph
    @17
    @3
    cr
    wcel
    wph
    @31
    @39
    @72
    wph
    @41
    wph
    @39
    @72
    simpll
    syldanl
    @31
    @72
    @17
    wph
    cN
    @1
    @6
    @5
    @15
    uztrn2
    adantll
    @29
    syl2anc
    rnmptssd
    cr
    cxr
    wss
    @32
    ressxr
    a1i
    sstrd
    3adant3
    @60
    @9
    supxrss
    syl2anc
    wph
    @55
    @11
    cli
    cdm
    #
    @56
    wph
    vn
    cZ
    @30
    cmpt
    @73
    wcel
    @55
    @73
    wcel
    smflimsuplem4.c
    wph
    cZ
    @30
    @5
    @30
    cvv
    cvv
    vn
    cN
    cvv
    cvv
    @5
    smflimsuplem4.1
    @14
    @15
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    smflimsuplem4.z
    fvexi
    a1i
    @21
    @42
    @0
    @25
    fvexd
    wph
    cN
    cuz
    fvexd
    wph
    vn
    @5
    @5
    smflimsuplem4.1
    @40
    ssdf
    @32
    @0
    @25
    fvexd
    @32
    @30
    eqidd
    climeldmeqmpt
    mpbid
    eqeltrrd
    climinf2mpt
    eqbrtrd
    climreclmpt
    eqeltrd
end
