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
include "csup.mm"
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
include "breq1d.mm"
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
include "supeq1d.mm"
include "ex.mm"
include "ralrimi.mm"
include "mpteq12f.mm"
include "fmptdf.mm"
include "smfsup.mm"
include "eqeltrd.mm"

theorem smfsupmpt
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
  assume smfsupmpt.n: |- F/ n ph
  assume smfsupmpt.x: |- F/ x ph
  assume smfsupmpt.y: |- F/ y ph
  assume smfsupmpt.m: |- ( ph -> M e. ZZ )
  assume smfsupmpt.z: |- Z = ( ZZ>= ` M )
  assume smfsupmpt.s: |- ( ph -> S e. SAlg )
  assume smfsupmpt.b: |- ( ( ph /\ n e. Z /\ x e. A ) -> B e. V )
  assume smfsupmpt.f: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfsupmpt.d: |- D = { x e. |^|_ n e. Z A | E. y e. RR A. n e. Z B <_ y }
  assume smfsupmpt.g: |- G = ( x e. D |-> sup ( ran ( n e. Z |-> B ) , RR , < ) )

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
    vy
    cv
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
    @4
    cdm
    #
    ciin
    #
    crab
    #
    vn
    cZ
    @5
    cmpt
    #
    crn
    #
    cr
    clt
    csup
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
    csup
    #
    cmpt
    #
    @16
    cG
    @21
    wceq
    wph
    smfsupmpt.g
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
    smfsupmpt.x
    wph
    cD
    cB
    @6
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
    smfsupmpt.d
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
    smfsupmpt.n
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @10
    @2
    cdm
    cA
    cA
    @31
    @4
    @2
    wph
    vn
    cZ
    @2
    @3
    @17
    wph
    @3
    eqidd
    smfsupmpt.f
    fvmpt2d
    #
    dmeqd
    @31
    vx
    @2
    cA
    cB
    cr
    wph
    @30
    vx
    smfsupmpt.x
    vx
    @1
    cZ
    vx
    @1
    nfcv
    #
    vx
    cZ
    nfcv
    #
    nfel
    nfan
    #
    @2
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
    smfsupmpt.s
    adantr
    wph
    @30
    @0
    cA
    wcel
    #
    cB
    cV
    wcel
    #
    smfsupmpt.b
    3expa
    smfsupmpt.f
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
    @4
    vx
    @1
    @3
    vx
    vn
    cZ
    @2
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
    smfsupmpt.x
    wph
    @0
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
    smfsupmpt.y
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
    smfsupmpt.n
    vn
    @0
    @11
    vn
    @0
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
    @0
    @10
    cA
    @41
    @30
    @0
    @10
    wcel
    wph
    vn
    @0
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
    @5
    @6
    cle
    @45
    @5
    @0
    @2
    cfv
    #
    cB
    wph
    @30
    @5
    @46
    wceq
    @37
    @31
    @0
    @4
    @2
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
    smfsupmpt.b
    vx
    cA
    cB
    cV
    @2
    @36
    fvmpt2
    syl2anc
    eqtr2d
    #
    breq1d
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
    smfsupmpt.x
    wph
    @0
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
    @5
    wph
    @48
    vn
    smfsupmpt.n
    vn
    @0
    cD
    @43
    vn
    cD
    @28
    smfsupmpt.d
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
    @5
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
    @0
    @27
    wcel
    #
    @30
    @37
    @48
    @51
    @30
    @48
    @0
    @28
    wcel
    #
    @51
    @48
    @52
    cD
    @28
    @0
    smfsupmpt.d
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
    @0
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
    supeq1d
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
    @3
    @16
    cM
    cZ
    vn
    cZ
    @2
    nfmpt1
    @40
    smfsupmpt.m
    smfsupmpt.z
    smfsupmpt.s
    wph
    vn
    cZ
    @2
    @17
    @3
    smfsupmpt.n
    smfsupmpt.f
    @3
    eqid
    fmptdf
    @12
    eqid
    @16
    eqid
    smfsup
    eqeltrd
end
