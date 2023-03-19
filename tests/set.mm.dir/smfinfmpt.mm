include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cdm.mm"
include "ciin.mm"
include "crab.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "csmblfn.mm"
include "wceq.mm"
include "a1i.mm"
include "wal.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "fvmpt2d.mm"
include "dmeqd.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfan.mm"
include "eqid.mm"
include "csalg.mm"
include "adantr.mm"
include "3expa.mm"
include "smffmpt.mm"
include "fvmptelrn.mm"
include "dmmptdf.mm"
include "3eqtrrd.mm"
include "iineq2d.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "rabeqf.mm"
include "syl.mm"
include "nfv.mm"
include "nfii1.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "eliinid.mm"
include "adantll.mm"
include "eqcomd.mm"
include "adantlr.mm"
include "eleqtrd.mm"
include "w3a.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "simp3.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "breq2d.mm"
include "syl3anc.mm"
include "ralbida.mm"
include "rexbid.mm"
include "rabbida.mm"
include "eqtrd.mm"
include "alrimi.mm"
include "nfra1.mm"
include "nfrex.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "rabidim1.mm"
include "wi.mm"
include "idi.mm"
include "mpteq2da.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "ex.mm"
include "ralrimi.mm"
include "mpteq12f.mm"
include "fmptdf.mm"
include "smfinf.mm"
include "eqeltrd.mm"

theorem smfinfmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  assume smfinfmpt.n: |- F/ n ph
  assume smfinfmpt.x: |- F/ x ph
  assume smfinfmpt.y: |- F/ y ph
  assume smfinfmpt.m: |- ( ph -> M e. ZZ )
  assume smfinfmpt.z: |- Z = ( ZZ>= ` M )
  assume smfinfmpt.s: |- ( ph -> S e. SAlg )
  assume smfinfmpt.b: |- ( ( ph /\ n e. Z /\ x e. A ) -> B e. V )
  assume smfinfmpt.f: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfinfmpt.d: |- D = { x e. |^|_ n e. Z A | E. y e. RR A. n e. Z y <_ B }
  assume smfinfmpt.g: |- G = ( x e. D |-> inf ( ran ( n e. Z |-> B ) , RR , < ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint S n
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint n x
  disjoint n y
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    vy
    cv
    #
    vx
    cv
    #
    vn
    cv
    #
    vn
    cZ
    vx
    cA
    cB
    cmpt
    #
    cmpt
    #
    cfv
    #
    cfv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vx
    vn
    cZ
    @5
    cdm
    #
    ciin
    #
    crab
    #
    vn
    cZ
    @6
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wph
    cG
    vx
    cD
    vn
    cZ
    cB
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cmpt
    #
    @16
    cG
    @21
    wceq
    wph
    smfinfmpt.g
    a1i
    wph
    cD
    @12
    wceq
    #
    vx
    wal
    @20
    @15
    wceq
    #
    vx
    cD
    wral
    @21
    @16
    wceq
    wph
    @22
    vx
    smfinfmpt.x
    wph
    cD
    @0
    cB
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vx
    vn
    cZ
    cA
    ciin
    #
    crab
    #
    @12
    cD
    @28
    wceq
    wph
    smfinfmpt.d
    a1i
    wph
    @28
    @26
    vx
    @11
    crab
    #
    @12
    wph
    @27
    @11
    wceq
    @28
    @29
    wceq
    wph
    vn
    cZ
    cA
    @10
    smfinfmpt.n
    wph
    @2
    cZ
    wcel
    #
    wa
    #
    @10
    @3
    cdm
    cA
    cA
    @31
    @5
    @3
    wph
    vn
    cZ
    @3
    @4
    @17
    wph
    @4
    eqidd
    smfinfmpt.f
    fvmpt2d
    #
    dmeqd
    @31
    vx
    @3
    cA
    cB
    cr
    wph
    @30
    vx
    smfinfmpt.x
    vx
    @2
    cZ
    vx
    @2
    nfcv
    #
    vx
    cZ
    nfcv
    #
    nfel
    nfan
    #
    @3
    eqid
    #
    @31
    vx
    cA
    cB
    cr
    @31
    vx
    cA
    cB
    cS
    cV
    @35
    wph
    cS
    csalg
    wcel
    @30
    smfinfmpt.s
    adantr
    wph
    @30
    @1
    cA
    wcel
    #
    cB
    cV
    wcel
    #
    smfinfmpt.b
    3expa
    smfinfmpt.f
    smffmpt
    fvmptelrn
    dmmptdf
    @31
    cA
    eqidd
    3eqtrrd
    #
    iineq2d
    @26
    vx
    @27
    @11
    vx
    @27
    nfcv
    vn
    vx
    cZ
    @10
    @34
    vx
    @5
    vx
    @2
    @4
    vx
    vn
    cZ
    @3
    @34
    vx
    cA
    cB
    nfmpt1
    nfmpt
    #
    @33
    nffv
    nfdm
    nfiin
    rabeqf
    syl
    wph
    @26
    @9
    vx
    @11
    smfinfmpt.x
    wph
    @1
    @11
    wcel
    #
    wa
    #
    @25
    @8
    vy
    cr
    wph
    @41
    vy
    smfinfmpt.y
    @41
    vy
    nfv
    nfan
    @42
    @24
    @7
    vn
    cZ
    wph
    @41
    vn
    smfinfmpt.n
    vn
    @1
    @11
    vn
    @1
    nfcv
    #
    vn
    cZ
    @10
    nfii1
    nfel
    nfan
    @42
    @30
    wa
    #
    wph
    @30
    @37
    @24
    @7
    wb
    wph
    @41
    @30
    simpll
    @42
    @30
    simpr
    @44
    @1
    @10
    cA
    @41
    @30
    @1
    @10
    wcel
    wph
    vn
    @1
    cZ
    @10
    eliinid
    adantll
    wph
    @30
    @10
    cA
    wceq
    @41
    @31
    cA
    @10
    @39
    eqcomd
    adantlr
    eleqtrd
    wph
    @30
    @37
    w3a
    #
    cB
    @6
    @0
    cle
    @45
    @6
    @1
    @3
    cfv
    #
    cB
    wph
    @30
    @6
    @46
    wceq
    @37
    @31
    @1
    @5
    @3
    @32
    fveq1d
    3adant3
    @45
    @37
    @38
    @46
    cB
    wceq
    wph
    @30
    @37
    simp3
    smfinfmpt.b
    vx
    cA
    cB
    cV
    @3
    @36
    fvmpt2
    syl2anc
    eqtr2d
    #
    breq2d
    syl3anc
    ralbida
    rexbid
    rabbida
    eqtrd
    eqtrd
    alrimi
    wph
    @23
    vx
    cD
    smfinfmpt.x
    wph
    @1
    cD
    wcel
    #
    @23
    wph
    @48
    wa
    #
    cr
    @19
    @14
    clt
    @49
    @18
    @13
    @49
    vn
    cZ
    cB
    @6
    wph
    @48
    vn
    smfinfmpt.n
    vn
    @1
    cD
    @43
    vn
    cD
    @28
    smfinfmpt.d
    @26
    vn
    vx
    @27
    @25
    vn
    vy
    cr
    vn
    cr
    nfcv
    @24
    vn
    cZ
    nfra1
    nfrex
    vn
    cZ
    cA
    nfii1
    nfrab
    nfcxfr
    nfel
    nfan
    @49
    @30
    wa
    wph
    @30
    @37
    cB
    @6
    wceq
    #
    wph
    @48
    @30
    simpll
    @49
    @30
    simpr
    @48
    @30
    @37
    wph
    @48
    @30
    wa
    @1
    @27
    wcel
    #
    @30
    @37
    @48
    @51
    @30
    @48
    @1
    @28
    wcel
    #
    @51
    @48
    @52
    cD
    @28
    @1
    smfinfmpt.d
    eleq2i
    biimpi
    @26
    vx
    @27
    rabidim1
    syl
    adantr
    @48
    @30
    simpr
    vn
    @1
    cZ
    cA
    eliinid
    syl2anc
    adantll
    @45
    @50
    wi
    @47
    idi
    syl3anc
    mpteq2da
    rneqd
    infeq1d
    ex
    ralrimi
    vx
    cD
    @20
    @12
    @15
    mpteq12f
    syl2anc
    eqtrd
    wph
    vx
    vy
    @12
    cS
    vn
    @4
    @16
    cM
    cZ
    vn
    cZ
    @3
    nfmpt1
    @40
    smfinfmpt.m
    smfinfmpt.z
    smfinfmpt.s
    wph
    vn
    cZ
    @3
    @17
    @4
    smfinfmpt.n
    smfinfmpt.f
    @4
    eqid
    fmptdf
    @12
    eqid
    @16
    eqid
    smfinf
    eqeltrd
end
