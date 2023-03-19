include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "clsp.mm"
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
include "syl3anc.mm"
include "eqtrd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "cz.mm"
include "3ad2ant1.mm"
include "eluzelz2.mm"
include "3ad2ant2.mm"
include "fvexd.mm"
include "syldan.mm"
include "limsupequzmpt.mm"
include "nfci.mm"
include "simp2.mm"
include "uzidd.mm"
include "limsupequzmpt2.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "jca.mm"
include "ex.mm"
include "simpl.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "simp3.mm"
include "impbid.mm"
include "rabbida3.mm"
include "eleq2i.mm"
include "rabidim1.mm"
include "syl.mm"
include "sylan2.mm"
include "mpteq12da.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "fmptd2f.mm"
include "smflimsup.mm"

theorem smflimsupmpt
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
  let cW: class W
  let cZ: class Z
  let vk: setvar k
  assume smflimsupmpt.p: |- F/ m ph
  assume smflimsupmpt.x: |- F/ x ph
  assume smflimsupmpt.n: |- F/ n ph
  assume smflimsupmpt.m: |- ( ph -> M e. ZZ )
  assume smflimsupmpt.z: |- Z = ( ZZ>= ` M )
  assume smflimsupmpt.s: |- ( ph -> S e. SAlg )
  assume smflimsupmpt.b: |- ( ( ph /\ m e. Z /\ x e. A ) -> B e. W )
  assume smflimsupmpt.f: |- ( ( ph /\ m e. Z ) -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smflimsupmpt.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) A | ( limsup ` ( m e. Z |-> B ) ) e. RR }
  assume smflimsupmpt.g: |- G = ( x e. D |-> ( limsup ` ( m e. Z |-> B ) ) )

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
    clsp
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
    clsp
    cfv
    #
    cmpt
    #
    @14
    cG
    @17
    wceq
    wph
    smflimsupmpt.g
    a1i
    wph
    vx
    cD
    @16
    @13
    @6
    smflimsupmpt.x
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
    smflimsupmpt.d
    a1i
    wph
    @18
    @7
    vx
    @20
    @12
    smflimsupmpt.x
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
    @25
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
    smflimsupmpt.n
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
    smflimsupmpt.p
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
    smflimsupmpt.z
    uztrn2
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
    @36
    @4
    @2
    @36
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
    @36
    @2
    @15
    smflimsupmpt.f
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
    @36
    vx
    @2
    cA
    cB
    cW
    wph
    @33
    vx
    smflimsupmpt.x
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
    cW
    wcel
    #
    smflimsupmpt.b
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
    @42
    @22
    @44
    wph
    @22
    @44
    vn
    @0
    cZ
    @19
    eliun
    biimpi
    adantl
    wph
    @44
    @42
    wi
    @22
    wph
    @43
    @42
    vn
    cZ
    smflimsupmpt.n
    @42
    vn
    nfv
    wph
    @28
    @43
    @42
    wph
    @28
    @43
    w3a
    #
    vm
    @9
    @5
    cmpt
    #
    clsp
    cfv
    vm
    @9
    cB
    cmpt
    #
    clsp
    cfv
    @6
    @16
    @45
    @46
    @47
    clsp
    @45
    vm
    @9
    @5
    cB
    wph
    @28
    @43
    vm
    smflimsupmpt.p
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
    @45
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
    @50
    wceq
    #
    @43
    @32
    wph
    @33
    @51
    @34
    @35
    @36
    @0
    @4
    @2
    @37
    fveq1d
    syl2anc
    3adantl3
    @49
    @39
    @40
    @50
    cB
    wceq
    @43
    wph
    @31
    @39
    @28
    vm
    @0
    @9
    cA
    eliinid
    3ad2antl3
    #
    @49
    wph
    @33
    @39
    @40
    wph
    @28
    @43
    @31
    simpl1
    wph
    @28
    @31
    @33
    @43
    @35
    3adantl3
    #
    @52
    smflimsupmpt.b
    syl3anc
    #
    vx
    cA
    cB
    cW
    @2
    @38
    fvmpt2
    syl2anc
    eqtrd
    mpteq2da
    fveq2d
    @45
    cZ
    @9
    @5
    vm
    cM
    @8
    cvv
    cvv
    @48
    wph
    @28
    cM
    cz
    wcel
    @43
    smflimsupmpt.m
    3ad2ant1
    @28
    wph
    @8
    cz
    wcel
    @43
    cM
    @8
    cZ
    smflimsupmpt.z
    eluzelz2
    3ad2ant2
    #
    smflimsupmpt.z
    @9
    eqid
    #
    @45
    @33
    wa
    @0
    @4
    fvexd
    #
    @45
    @31
    @33
    @5
    cvv
    wcel
    @53
    @57
    syldan
    limsupequzmpt
    @45
    cZ
    @9
    cB
    vm
    @8
    cM
    @8
    cW
    @48
    vm
    vn
    cZ
    @30
    nfci
    vm
    @9
    nfcv
    smflimsupmpt.z
    @56
    wph
    @28
    @43
    simp2
    @45
    @8
    @55
    uzidd
    @54
    limsupequzmpt2
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
    ex
    wph
    @25
    @23
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
    @41
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
    @59
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
    @58
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
    ex
    impbid
    rabbida3
    eqtrd
    @0
    cD
    wcel
    #
    wph
    @22
    @60
    @62
    @0
    @21
    wcel
    #
    @22
    @62
    @63
    cD
    @21
    @0
    smflimsupmpt.d
    eleq2i
    biimpi
    @18
    vx
    @20
    rabidim1
    syl
    @61
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
    smflimsupmpt.m
    smflimsupmpt.z
    smflimsupmpt.s
    wph
    vm
    cZ
    @2
    @15
    smflimsupmpt.p
    smflimsupmpt.f
    fmptd2f
    @13
    eqid
    @14
    eqid
    smflimsup
    eqeltrd
end
