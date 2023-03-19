include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cdm.mm"
include "ciin.mm"
include "wcel.mm"
include "wrex.mm"
include "cmpt.mm"
include "cli.mm"
include "cr.mm"
include "ciun.mm"
include "crab.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfiun.mm"
include "ssrab2f.mm"
include "eqsstri.mm"
include "sseli.mm"
include "eliun.mm"
include "sylib.mm"
include "syl.mm"
include "nfv.mm"
include "w3a.mm"
include "cvv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nf3an.mm"
include "cz.mm"
include "uzssz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "sseldi.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wss.mm"
include "uztrn2.mm"
include "ssd.mm"
include "wa.mm"
include "fvexd.mm"
include "simpr.mm"
include "eqidd.mm"
include "climfveqmpt.mm"
include "wbr.mm"
include "nfmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "elrabf.mm"
include "simprd.mm"
include "adantr.mm"
include "nfmpt1.mm"
include "nfci.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfan.mm"
include "adantl.mm"
include "ssid.mm"
include "climeldmeqmpt.mm"
include "mpbid.mm"
include "climdm.mm"
include "sylan.mm"
include "3adant3.mm"
include "simpl1.mm"
include "simpl2.mm"
include "dmeqd.mm"
include "cbviin.mm"
include "eliinid.mm"
include "syl2anc.mm"
include "3ad2antl3.mm"
include "id.mm"
include "fveq1d.mm"
include "fvmptf.mm"
include "wf.mm"
include "simpll.mm"
include "adantll.mm"
include "wi.mm"
include "nff.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "3adantl3.mm"
include "simpl3.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "syl31anc.mm"
include "climrecl.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem fnlimfvre
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  assume fnlimfvre.p: |- F/ m ph
  assume fnlimfvre.m: |- F/_ m F
  assume fnlimfvre.n: |- F/_ x F
  assume fnlimfvre.z: |- Z = ( ZZ>= ` M )
  assume fnlimfvre.f: |- ( ( ph /\ m e. Z ) -> ( F ` m ) : dom ( F ` m ) --> RR )
  assume fnlimfvre.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume fnlimfvre.x: |- ( ph -> X e. D )

  disjoint F n
  disjoint X m
  disjoint X n
  disjoint m n
  disjoint X x
  disjoint m x
  disjoint n x
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint n ph
  disjoint F j
  disjoint j n
  disjoint X j
  disjoint j m
  disjoint Z j
  disjoint j ph
  assert |- ( ph -> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` X ) ) ) e. RR )

  proof
    wph
    cX
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    vm
    cv
    #
    cF
    cfv
    #
    cdm
    #
    ciin
    #
    wcel
    #
    vn
    cZ
    wrex
    #
    vm
    cZ
    cX
    @3
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cr
    wcel
    #
    wph
    cX
    cD
    wcel
    #
    @7
    fnlimfvre.x
    @12
    cX
    vn
    cZ
    @5
    ciun
    #
    wcel
    #
    @7
    cD
    @13
    cX
    cD
    vm
    cZ
    vx
    cv
    #
    @3
    cfv
    #
    cmpt
    #
    cli
    cdm
    #
    wcel
    #
    vx
    @13
    crab
    #
    @13
    fnlimfvre.d
    @19
    vx
    @13
    vn
    vx
    cZ
    @5
    vx
    cZ
    nfcv
    #
    vm
    vx
    @1
    @4
    vx
    @1
    nfcv
    vx
    @3
    vx
    @2
    cF
    fnlimfvre.n
    vx
    @2
    nfcv
    nffv
    #
    nfdm
    nfiin
    nfiun
    #
    ssrab2f
    eqsstri
    sseli
    vn
    cX
    cZ
    @5
    eliun
    sylib
    syl
    wph
    @6
    @11
    vn
    cZ
    wph
    vn
    nfv
    @11
    vn
    nfv
    wph
    @0
    cZ
    wcel
    #
    @6
    @11
    wph
    @24
    @6
    w3a
    #
    @10
    vm
    @1
    @8
    cmpt
    #
    cli
    cfv
    #
    cr
    @25
    cZ
    @8
    @1
    @8
    cvv
    cvv
    vm
    @0
    cvv
    cvv
    @1
    wph
    @24
    @6
    vm
    fnlimfvre.p
    @24
    vm
    nfv
    #
    vm
    cX
    @5
    vm
    cX
    nfcv
    #
    vm
    @1
    @4
    nfii1
    #
    nfel
    nf3an
    @24
    wph
    @0
    cz
    wcel
    #
    @6
    @24
    cM
    cuz
    cfv
    #
    cz
    @0
    cM
    uzssz
    @24
    @0
    @32
    wcel
    cZ
    @32
    @0
    fnlimfvre.z
    eleq2i
    biimpi
    sseldi
    #
    3ad2ant2
    #
    @1
    eqid
    #
    cZ
    cvv
    wcel
    #
    @25
    cZ
    @32
    cvv
    fnlimfvre.z
    cM
    cuz
    fvex
    eqeltri
    #
    a1i
    @24
    wph
    @1
    cZ
    wss
    #
    @6
    @24
    vj
    @1
    cZ
    cM
    vj
    cv
    #
    @0
    cZ
    fnlimfvre.z
    uztrn2
    #
    ssd
    #
    3ad2ant2
    @25
    @2
    cZ
    wcel
    #
    wa
    cX
    @3
    fvexd
    @25
    @0
    cuz
    fvexd
    @25
    vj
    @1
    @1
    @25
    @39
    @1
    wcel
    #
    simpr
    #
    ssd
    @25
    @2
    @1
    wcel
    #
    wa
    #
    cX
    @3
    fvexd
    @46
    @8
    eqidd
    climfveqmpt
    @25
    @27
    vj
    @26
    @0
    @1
    @35
    @34
    wph
    @24
    @26
    @27
    cli
    wbr
    #
    @6
    wph
    @12
    @24
    @47
    fnlimfvre.x
    @12
    @24
    wa
    #
    @26
    @18
    wcel
    #
    @47
    @48
    @9
    @18
    wcel
    #
    @49
    @12
    @50
    @24
    @12
    cX
    @20
    wcel
    #
    @50
    @12
    @51
    cD
    @20
    cX
    fnlimfvre.d
    eleq2i
    biimpi
    @51
    @14
    @50
    @51
    @14
    @50
    wa
    @19
    @50
    vx
    cX
    @13
    vx
    cX
    nfcv
    #
    @23
    vx
    @9
    @18
    vx
    vm
    cZ
    @8
    @21
    vx
    cX
    @3
    @22
    @52
    nffv
    nfmpt
    vx
    @18
    nfcv
    nfel
    @15
    cX
    wceq
    #
    @17
    @9
    @18
    @53
    vm
    cZ
    @16
    @8
    @15
    cX
    @3
    fveq2
    mpteq2dv
    eleq1d
    elrabf
    biimpi
    simprd
    syl
    adantr
    @48
    cZ
    @8
    @1
    @8
    cvv
    cvv
    vm
    @0
    cvv
    cvv
    @1
    @12
    @24
    vm
    vm
    cX
    cD
    @29
    vm
    cD
    @20
    fnlimfvre.d
    @19
    vm
    vx
    @13
    vm
    @17
    @18
    vm
    cZ
    @16
    nfmpt1
    vm
    @18
    nfcv
    nfel
    vn
    vm
    cZ
    @5
    vm
    vj
    cZ
    @39
    cZ
    wcel
    #
    vm
    nfv
    #
    nfci
    @30
    nfiun
    nfrab
    nfcxfr
    nfel
    @28
    nfan
    @24
    @31
    @12
    @33
    adantl
    @35
    @36
    @48
    @37
    a1i
    @24
    @38
    @12
    @41
    adantl
    @48
    @42
    wa
    cX
    @3
    fvexd
    @48
    @0
    cuz
    fvexd
    @1
    @1
    wss
    @48
    @1
    ssid
    a1i
    @48
    @45
    wa
    #
    cX
    @3
    fvexd
    @56
    @8
    eqidd
    climeldmeqmpt
    mpbid
    @26
    climdm
    sylib
    sylan
    3adant3
    @25
    @43
    wa
    wph
    @24
    cX
    @39
    cF
    cfv
    #
    cdm
    #
    wcel
    #
    @43
    @39
    @26
    cfv
    #
    cr
    wcel
    wph
    @24
    @6
    @43
    simpl1
    wph
    @24
    @6
    @43
    simpl2
    @6
    wph
    @43
    @59
    @24
    @6
    @43
    wa
    cX
    vj
    @1
    @58
    ciin
    #
    wcel
    #
    @43
    @59
    @6
    @62
    @43
    @6
    @62
    @5
    @61
    cX
    vm
    vj
    @1
    @4
    @58
    vj
    @4
    nfcv
    vm
    @57
    vm
    @39
    cF
    fnlimfvre.m
    vm
    @39
    nfcv
    #
    nffv
    #
    nfdm
    #
    @2
    @39
    wceq
    #
    @3
    @57
    @2
    @39
    cF
    fveq2
    #
    dmeqd
    #
    cbviin
    eleq2i
    biimpi
    adantr
    @6
    @43
    simpr
    vj
    cX
    @1
    @58
    eliinid
    syl2anc
    3ad2antl3
    @44
    wph
    @24
    @59
    w3a
    #
    @43
    wa
    #
    @60
    cX
    @57
    cfv
    #
    cr
    @43
    @60
    @71
    wceq
    #
    @69
    @43
    @43
    @71
    cvv
    wcel
    @72
    @43
    id
    @43
    cX
    @57
    fvexd
    vm
    @39
    @8
    @71
    @1
    @26
    cvv
    @63
    vm
    cX
    @57
    @64
    @29
    nffv
    @66
    cX
    @3
    @57
    @67
    fveq1d
    @26
    eqid
    fvmptf
    syl2anc
    adantl
    @70
    @58
    cr
    cX
    @57
    wph
    @24
    @43
    @58
    cr
    @57
    wf
    #
    @59
    wph
    @24
    wa
    @43
    wa
    wph
    @54
    @73
    wph
    @24
    @43
    simpll
    @24
    @43
    @54
    wph
    @40
    adantll
    wph
    @42
    wa
    #
    @4
    cr
    @3
    wf
    #
    wi
    wph
    @54
    wa
    #
    @73
    wi
    vm
    vj
    @76
    @73
    vm
    wph
    @54
    vm
    fnlimfvre.p
    @55
    nfan
    vm
    @58
    cr
    @57
    @64
    @65
    vm
    cr
    nfcv
    nff
    nfim
    @66
    @74
    @76
    @75
    @73
    @66
    @42
    @54
    wph
    @2
    @39
    cZ
    eleq1
    anbi2d
    @66
    @4
    @58
    cr
    @3
    @57
    @67
    @68
    feq12d
    imbi12d
    fnlimfvre.f
    chvar
    syl2anc
    3adantl3
    wph
    @24
    @59
    @43
    simpl3
    ffvelrnd
    eqeltrd
    syl31anc
    climrecl
    eqeltrd
    3exp
    rexlimd
    mpd
end
