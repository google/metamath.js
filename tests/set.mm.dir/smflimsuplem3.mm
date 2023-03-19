include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "cmpt.mm"
include "cli.mm"
include "wcel.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "cvv.mm"
include "nfv.mm"
include "wa.mm"
include "fvex.mm"
include "dmex.mm"
include "a1i.mm"
include "w3a.mm"
include "fvexd.mm"
include "csmblfn.mm"
include "cr.mm"
include "csalg.mm"
include "adantr.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cres.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "wceq.mm"
include "eqid.mm"
include "eluzelz2.mm"
include "uzn0d.mm"
include "wral.mm"
include "rgenw.mm"
include "iinexd.mm"
include "adantl.mm"
include "rabexd.mm"
include "fvmpt2d.mm"
include "fvres.mm"
include "eqcomd.mm"
include "dmeqd.mm"
include "iineq2dv.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "mpteq2ia.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "eqtrd.mm"
include "mpteq12df.mm"
include "cz.mm"
include "wf.mm"
include "wss.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "uzss.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "fssresd.mm"
include "smfsupxr.mm"
include "eqeltrd.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "smff.mm"
include "feqmptd.mm"
include "smflimmpt.mm"

theorem smflimsuplem3
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cZ: class Z
  assume smflimsuplem3.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem3.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem3.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem3.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem3.e: |- E = ( n e. Z |-> { x e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem3.h: |- H = ( n e. Z |-> ( x e. ( E ` n ) |-> sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )

  disjoint E x
  disjoint F m
  disjoint F x
  disjoint m x
  disjoint H k
  disjoint H x
  disjoint k x
  disjoint S k
  disjoint S n
  disjoint k n
  disjoint Z k
  disjoint Z n
  disjoint Z x
  disjoint n x
  disjoint Z m
  disjoint m n
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint m ph
  disjoint k x
  assert |- ( ph -> ( x e. { x e. U_ k e. Z |^|_ n e. ( ZZ>= ` k ) dom ( H ` n ) | ( n e. Z |-> ( ( H ` n ) ` x ) ) e. dom ~~> } |-> ( ~~> ` ( n e. Z |-> ( ( H ` n ) ` x ) ) ) ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    vn
    cv
    #
    cH
    cfv
    #
    cdm
    #
    vx
    cv
    #
    @1
    cfv
    #
    vn
    cZ
    @4
    cmpt
    #
    cli
    cdm
    wcel
    vx
    vk
    cZ
    vn
    vk
    cv
    cuz
    cfv
    @2
    ciin
    ciun
    crab
    #
    cS
    vn
    vk
    vx
    @6
    @5
    cli
    cfv
    cmpt
    #
    cM
    cvv
    cvv
    cZ
    wph
    vn
    nfv
    wph
    vx
    nfv
    wph
    vk
    nfv
    smflimsuplem3.m
    smflimsuplem3.z
    @2
    cvv
    wcel
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    @0
    cH
    fvex
    dmex
    a1i
    wph
    @8
    @3
    @2
    wcel
    w3a
    @3
    @1
    fvexd
    smflimsuplem3.s
    @9
    vx
    @2
    @4
    cmpt
    #
    @1
    cS
    csmblfn
    cfv
    #
    @9
    @1
    @10
    @9
    vx
    @2
    cr
    @1
    @9
    @2
    cS
    @1
    wph
    cS
    csalg
    wcel
    @8
    smflimsuplem3.s
    adantr
    #
    wph
    cZ
    @11
    @0
    cH
    wph
    vn
    cZ
    vx
    @0
    cE
    cfv
    #
    vm
    @0
    cuz
    cfv
    #
    @3
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
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
    @11
    cH
    @9
    @21
    vx
    vm
    @14
    @3
    @15
    cF
    @14
    cres
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vx
    vm
    @14
    @23
    cdm
    #
    ciin
    #
    crab
    #
    @27
    cmpt
    #
    @11
    @9
    vx
    @13
    @20
    @31
    @27
    @9
    vx
    nfv
    vx
    @13
    nfcv
    @28
    vx
    @30
    nfrab1
    @9
    @13
    @20
    cr
    wcel
    #
    vx
    vm
    @14
    @16
    cdm
    #
    ciin
    #
    crab
    #
    @31
    wph
    vn
    cZ
    @36
    cE
    cvv
    cE
    vn
    cZ
    @36
    cmpt
    wceq
    wph
    smflimsuplem3.e
    a1i
    @9
    @33
    vx
    @35
    @36
    cvv
    @36
    eqid
    @8
    @35
    cvv
    wcel
    wph
    @8
    vm
    @14
    @34
    cvv
    @8
    @0
    @14
    cM
    @0
    cZ
    smflimsuplem3.z
    eluzelz2
    #
    @14
    eqid
    #
    uzn0d
    @34
    cvv
    wcel
    #
    vm
    @14
    wral
    @8
    @39
    vm
    @14
    @16
    @15
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    adantl
    rabexd
    fvmpt2d
    @9
    @33
    @28
    vx
    @35
    @30
    @9
    @3
    @35
    wcel
    @3
    @30
    wcel
    @33
    @28
    @9
    @35
    @30
    @3
    @9
    vm
    @14
    @34
    @29
    @9
    @15
    @14
    wcel
    #
    wa
    @16
    @23
    @40
    @16
    @23
    wceq
    @9
    @40
    @23
    @16
    @15
    @14
    cF
    fvres
    eqcomd
    #
    adantl
    dmeqd
    iineq2dv
    eleq2d
    @9
    @20
    @27
    cr
    @20
    @27
    wceq
    @9
    cxr
    @19
    @26
    clt
    @18
    @25
    vm
    @14
    @17
    @24
    @40
    @3
    @16
    @23
    @41
    fveq1d
    mpteq2ia
    rneqi
    supeq1i
    a1i
    #
    eleq1d
    anbi12d
    rabbidva2
    eqtrd
    @42
    mpteq12df
    @9
    vx
    @31
    cS
    vm
    @22
    @32
    @0
    @14
    vm
    @22
    nfcv
    vx
    @22
    nfcv
    @8
    @0
    cz
    wcel
    wph
    @37
    adantl
    @38
    @12
    @9
    cZ
    @11
    @14
    cF
    wph
    cZ
    @11
    cF
    wf
    @8
    smflimsuplem3.f
    adantr
    @8
    @14
    cZ
    wss
    wph
    @8
    @14
    cM
    cuz
    cfv
    #
    cZ
    @8
    @0
    @43
    wcel
    #
    @14
    @43
    wss
    @8
    @44
    cZ
    @43
    @0
    smflimsuplem3.z
    eleq2i
    biimpi
    cM
    @0
    uzss
    syl
    smflimsuplem3.z
    syl6sseqr
    adantl
    fssresd
    @31
    eqid
    @32
    eqid
    smfsupxr
    eqeltrd
    smflimsuplem3.h
    fmptd
    ffvelrnda
    #
    @2
    eqid
    smff
    feqmptd
    eqcomd
    @45
    eqeltrd
    @6
    eqid
    @7
    eqid
    smflimmpt
end
