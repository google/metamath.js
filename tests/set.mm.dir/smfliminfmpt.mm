include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "clsi.mm"
include "cr.mm"
include "wcel.mm"
include "cuz.mm"
include "cdm.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "csmblfn.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "nfv.mm"
include "nfan.mm"
include "simpll.mm"
include "uztrn2.mm"
include "adantll.mm"
include "cvv.mm"
include "elexd.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "dmeqd.mm"
include "3expa.mm"
include "dmmptdf.mm"
include "eqtr2d.mm"
include "iineq2d.mm"
include "iuneq2df.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "adantrr.mm"
include "wrex.mm"
include "eliun.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nf3an.mm"
include "fveq1d.mm"
include "3adantl3.mm"
include "eliinid.mm"
include "3ad2antl3.mm"
include "simpl1.mm"
include "simp2.mm"
include "sylan.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "eluzelz2.mm"
include "uzidd.mm"
include "3ad2ant2.mm"
include "fvexd.mm"
include "liminfequzmpt2.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "jca.mm"
include "simpl.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "simp3.mm"
include "impbida.mm"
include "rabbida3.mm"
include "eleq2i.mm"
include "rabidim1.mm"
include "syl.mm"
include "sylan2.mm"
include "mpteq12da.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "fmptd2f.mm"
include "smfliminf.mm"

theorem smfliminfmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  assume smfliminfmpt.p: |- F/ m ph
  assume smfliminfmpt.x: |- F/ x ph
  assume smfliminfmpt.n: |- F/ n ph
  assume smfliminfmpt.m: |- ( ph -> M e. ZZ )
  assume smfliminfmpt.z: |- Z = ( ZZ>= ` M )
  assume smfliminfmpt.s: |- ( ph -> S e. SAlg )
  assume smfliminfmpt.b: |- ( ( ph /\ m e. Z /\ x e. A ) -> B e. V )
  assume smfliminfmpt.f: |- ( ( ph /\ m e. Z ) -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfliminfmpt.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) A | ( liminf ` ( m e. Z |-> B ) ) e. RR }
  assume smfliminfmpt.g: |- G = ( x e. D |-> ( liminf ` ( m e. Z |-> B ) ) )

  disjoint A n
  disjoint A x
  disjoint n x
  disjoint B n
  disjoint M m
  disjoint S m
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m n
  disjoint m x
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    vm
    cZ
    vx
    cv
    #
    vm
    cv
    #
    vm
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
    cmpt
    clsi
    cfv
    #
    cr
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @4
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    @6
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
    vm
    cZ
    cB
    cmpt
    clsi
    cfv
    #
    cmpt
    #
    @14
    cG
    @17
    wceq
    wph
    smfliminfmpt.g
    a1i
    wph
    vx
    cD
    @16
    @13
    @6
    smfliminfmpt.x
    wph
    cD
    @16
    cr
    wcel
    #
    vx
    vn
    cZ
    vm
    @9
    cA
    ciin
    #
    ciun
    #
    crab
    #
    @13
    cD
    @21
    wceq
    wph
    smfliminfmpt.d
    a1i
    wph
    @18
    @7
    vx
    @20
    @12
    smfliminfmpt.x
    wph
    @0
    @20
    wcel
    #
    @18
    wa
    #
    @0
    @12
    wcel
    #
    @7
    wa
    #
    wph
    @23
    wa
    #
    @24
    @7
    wph
    @22
    @24
    @18
    wph
    @22
    wa
    #
    @0
    @20
    @12
    wph
    @22
    simpr
    wph
    @20
    @12
    wceq
    @22
    wph
    vn
    cZ
    @19
    @11
    smfliminfmpt.n
    wph
    @8
    cZ
    wcel
    #
    wa
    #
    vm
    @9
    cA
    @10
    wph
    @28
    vm
    smfliminfmpt.p
    @28
    vm
    nfv
    #
    nfan
    @29
    @1
    @9
    wcel
    #
    wa
    #
    wph
    @1
    cZ
    wcel
    #
    cA
    @10
    wceq
    wph
    @28
    @31
    simpll
    #
    @28
    @31
    @33
    wph
    cM
    @1
    @8
    cZ
    smfliminfmpt.z
    uztrn2
    #
    adantll
    #
    wph
    @33
    wa
    #
    @10
    @2
    cdm
    cA
    @37
    @4
    @2
    @37
    @33
    @2
    cvv
    wcel
    @4
    @2
    wceq
    wph
    @33
    simpr
    @37
    @2
    @15
    smfliminfmpt.f
    elexd
    vm
    cZ
    @2
    cvv
    @3
    @3
    eqid
    fvmpt2
    syl2anc
    #
    dmeqd
    @37
    vx
    @2
    cA
    cB
    cV
    wph
    @33
    vx
    smfliminfmpt.x
    @33
    vx
    nfv
    nfan
    @2
    eqid
    #
    wph
    @33
    @0
    cA
    wcel
    #
    cB
    cV
    wcel
    #
    smfliminfmpt.b
    3expa
    dmmptdf
    eqtr2d
    syl2anc
    iineq2d
    iuneq2df
    #
    adantr
    eleqtrd
    adantrr
    @26
    @6
    @16
    cr
    wph
    @22
    @6
    @16
    wceq
    #
    @18
    @27
    @0
    @19
    wcel
    #
    vn
    cZ
    wrex
    #
    @43
    @22
    @45
    wph
    @22
    @45
    vn
    @0
    cZ
    @19
    eliun
    biimpi
    adantl
    wph
    @45
    @43
    wi
    @22
    wph
    @44
    @43
    vn
    cZ
    smfliminfmpt.n
    @43
    vn
    nfv
    wph
    @28
    @44
    @43
    wph
    @28
    @44
    w3a
    #
    vm
    @9
    @5
    cmpt
    #
    clsi
    cfv
    vm
    @9
    cB
    cmpt
    #
    clsi
    cfv
    @6
    @16
    @46
    @47
    @48
    clsi
    @46
    vm
    @9
    @5
    cB
    wph
    @28
    @44
    vm
    smfliminfmpt.p
    @30
    vm
    @0
    @19
    vm
    @0
    nfcv
    vm
    @9
    cA
    nfii1
    nfel
    nf3an
    #
    @46
    @31
    wa
    #
    @5
    @0
    @2
    cfv
    #
    cB
    wph
    @28
    @31
    @5
    @51
    wceq
    #
    @44
    @32
    wph
    @33
    @52
    @34
    @36
    @37
    @0
    @4
    @2
    @38
    fveq1d
    syl2anc
    3adantl3
    @50
    @40
    @41
    @51
    cB
    wceq
    @44
    wph
    @31
    @40
    @28
    vm
    @0
    @9
    cA
    eliinid
    3ad2antl3
    #
    @50
    wph
    @33
    @40
    @41
    wph
    @28
    @44
    @31
    simpl1
    @46
    @28
    @31
    @33
    wph
    @28
    @44
    simp2
    #
    @35
    sylan
    @53
    smfliminfmpt.b
    syl3anc
    #
    vx
    cA
    cB
    cV
    @2
    @39
    fvmpt2
    syl2anc
    eqtrd
    mpteq2da
    fveq2d
    @46
    cZ
    @9
    @5
    vm
    @8
    cM
    @8
    cvv
    @49
    vm
    cZ
    nfcv
    #
    vm
    @9
    nfcv
    #
    smfliminfmpt.z
    @9
    eqid
    #
    @54
    @28
    wph
    @8
    @9
    wcel
    @44
    @28
    @8
    cM
    @8
    cZ
    smfliminfmpt.z
    eluzelz2
    uzidd
    3ad2ant2
    #
    @50
    @0
    @4
    fvexd
    liminfequzmpt2
    @46
    cZ
    @9
    cB
    vm
    @8
    cM
    @8
    cV
    @49
    @56
    @57
    smfliminfmpt.z
    @58
    @54
    @59
    @55
    liminfequzmpt2
    3eqtr4d
    3exp
    rexlimd
    adantr
    mpd
    #
    adantrr
    wph
    @22
    @18
    simprr
    eqeltrd
    jca
    wph
    @25
    wa
    wph
    @22
    @7
    @23
    wph
    @25
    simpl
    wph
    @24
    @22
    @7
    wph
    @24
    wa
    @0
    @12
    @20
    wph
    @24
    simpr
    wph
    @12
    @20
    wceq
    @24
    wph
    @20
    @12
    @42
    eqcomd
    adantr
    eleqtrd
    adantrr
    wph
    @24
    @7
    simprr
    wph
    @22
    @7
    w3a
    #
    @22
    @18
    wph
    @22
    @7
    simp2
    @61
    @16
    @6
    cr
    wph
    @22
    @16
    @6
    wceq
    #
    @7
    @27
    @6
    @16
    @60
    eqcomd
    #
    3adant3
    wph
    @22
    @7
    simp3
    eqeltrd
    jca
    syl3anc
    impbida
    rabbida3
    eqtrd
    @0
    cD
    wcel
    #
    wph
    @22
    @62
    @64
    @0
    @21
    wcel
    #
    @22
    @64
    @65
    cD
    @21
    @0
    smfliminfmpt.d
    eleq2i
    biimpi
    @18
    vx
    @20
    rabidim1
    syl
    @63
    sylan2
    mpteq12da
    eqtrd
    wph
    vx
    @13
    cS
    vm
    vn
    @3
    @14
    cM
    cZ
    vm
    cZ
    @2
    nfmpt1
    vx
    vm
    cZ
    @2
    vx
    cZ
    nfcv
    vx
    cA
    cB
    nfmpt1
    nfmpt
    smfliminfmpt.m
    smfliminfmpt.z
    smfliminfmpt.s
    wph
    vm
    cZ
    @2
    @15
    smfliminfmpt.p
    smfliminfmpt.f
    fmptd2f
    @13
    eqid
    @14
    eqid
    smfliminf
    eqeltrd
end
