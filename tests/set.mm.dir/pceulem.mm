include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "simprd.mm"
include "nncnd.mm"
include "simpld.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "cdiv.mm"
include "eqtr3d.mm"
include "nnne0d.mm"
include "divmuleqd.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "oveq2.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "3eqtr4g.mm"
include "supeq1d.mm"
include "cprime.mm"
include "cc0.mm"
include "wne.mm"
include "nnzd.mm"
include "div0d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "sylibrd.mm"
include "necon3d.mm"
include "mpd.mm"
include "eqid.mm"
include "pcpremul.mm"
include "syl122anc.mm"
include "3eqtr4d.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "syl.mm"
include "wa.mm"
include "pcprecl.mm"
include "syl12anc.mm"
include "nn0cnd.mm"
include "addsubeq4d.mm"

theorem pceulem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cN: class N
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  assume pcval.1: |- S = sup ( { n e. NN0 | ( P ^ n ) || x } , RR , < )
  assume pcval.2: |- T = sup ( { n e. NN0 | ( P ^ n ) || y } , RR , < )
  assume pceu.3: |- U = sup ( { n e. NN0 | ( P ^ n ) || s } , RR , < )
  assume pceu.4: |- V = sup ( { n e. NN0 | ( P ^ n ) || t } , RR , < )
  assume pceu.5: |- ( ph -> P e. Prime )
  assume pceu.6: |- ( ph -> N =/= 0 )
  assume pceu.7: |- ( ph -> ( x e. ZZ /\ y e. NN ) )
  assume pceu.8: |- ( ph -> N = ( x / y ) )
  assume pceu.9: |- ( ph -> ( s e. ZZ /\ t e. NN ) )
  assume pceu.10: |- ( ph -> N = ( s / t ) )

  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint N s
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint P n
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint S s
  disjoint S t
  disjoint T s
  disjoint T t
  disjoint n p
  disjoint n r
  disjoint n w
  disjoint n z
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint N p
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint N r
  disjoint s w
  disjoint s z
  disjoint t w
  disjoint t z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint N w
  disjoint x z
  disjoint y z
  disjoint N z
  disjoint P p
  disjoint P r
  disjoint P w
  disjoint P z
  disjoint S p
  disjoint S r
  disjoint S w
  disjoint S z
  disjoint T p
  disjoint T r
  disjoint T w
  disjoint T z
  disjoint ph z
  assert |- ( ph -> ( S - T ) = ( U - V ) )

  proof
    wph
    cT
    cU
    caddc
    co
    #
    cS
    cV
    caddc
    co
    #
    wceq
    cS
    cT
    cmin
    co
    cU
    cV
    cmin
    co
    wceq
    wph
    cP
    vn
    cv
    #
    cexp
    co
    #
    vy
    cv
    #
    vs
    cv
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @3
    vx
    cv
    #
    vt
    cv
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @0
    @1
    wph
    cr
    @8
    @14
    clt
    wph
    cP
    vz
    cv
    #
    cexp
    co
    #
    @6
    cdvds
    wbr
    #
    vz
    cn0
    crab
    @17
    @12
    cdvds
    wbr
    #
    vz
    cn0
    crab
    @8
    @14
    wph
    @18
    @19
    vz
    cn0
    wph
    @6
    @12
    @17
    cdvds
    wph
    @6
    @5
    @4
    cmul
    co
    #
    @12
    wph
    @4
    @5
    wph
    @4
    wph
    @10
    cz
    wcel
    #
    @4
    cn
    wcel
    #
    pceu.7
    simprd
    #
    nncnd
    #
    wph
    @5
    wph
    @5
    cz
    wcel
    #
    @11
    cn
    wcel
    #
    pceu.9
    simpld
    #
    zcnd
    #
    mulcomd
    wph
    @5
    @11
    cdiv
    co
    #
    @10
    @4
    cdiv
    co
    #
    wceq
    @20
    @12
    wceq
    wph
    cN
    @29
    @30
    pceu.10
    pceu.8
    eqtr3d
    wph
    @5
    @11
    @10
    @4
    @28
    wph
    @11
    wph
    @25
    @26
    pceu.9
    simprd
    #
    nncnd
    #
    wph
    @10
    wph
    @21
    @22
    pceu.7
    simpld
    #
    zcnd
    @24
    wph
    @11
    @31
    nnne0d
    #
    wph
    @4
    @23
    nnne0d
    #
    divmuleqd
    mpbid
    eqtrd
    breq2d
    rabbidv
    @7
    @18
    vn
    vz
    cn0
    @2
    @16
    wceq
    #
    @3
    @17
    @6
    cdvds
    @2
    @16
    cP
    cexp
    oveq2
    #
    breq1d
    cbvrabv
    @13
    @19
    vn
    vz
    cn0
    @36
    @3
    @17
    @12
    cdvds
    @37
    breq1d
    cbvrabv
    3eqtr4g
    supeq1d
    wph
    cP
    cprime
    wcel
    #
    @4
    cz
    wcel
    #
    @4
    cc0
    wne
    #
    @25
    @5
    cc0
    wne
    #
    @0
    @9
    wceq
    pceu.5
    wph
    @4
    @23
    nnzd
    #
    @35
    @27
    wph
    cN
    cc0
    wne
    #
    @41
    pceu.6
    wph
    @5
    cc0
    cN
    cc0
    wph
    @5
    cc0
    wceq
    #
    @29
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wph
    @45
    @44
    cc0
    @11
    cdiv
    co
    #
    cc0
    wceq
    wph
    @11
    @32
    @34
    div0d
    @44
    @29
    @47
    cc0
    @5
    cc0
    @11
    cdiv
    oveq1
    eqeq1d
    syl5ibrcom
    wph
    cN
    @29
    cc0
    pceu.10
    eqeq1d
    sylibrd
    necon3d
    mpd
    #
    cP
    cT
    cU
    @9
    vn
    @4
    @5
    pcval.2
    pceu.3
    @9
    eqid
    pcpremul
    syl122anc
    wph
    @38
    @21
    @10
    cc0
    wne
    #
    @11
    cz
    wcel
    #
    @11
    cc0
    wne
    #
    @1
    @15
    wceq
    pceu.5
    @33
    wph
    @43
    @49
    pceu.6
    wph
    @10
    cc0
    cN
    cc0
    wph
    @10
    cc0
    wceq
    #
    @30
    cc0
    wceq
    #
    @46
    wph
    @53
    @52
    cc0
    @4
    cdiv
    co
    #
    cc0
    wceq
    wph
    @4
    @24
    @35
    div0d
    @52
    @30
    @54
    cc0
    @10
    cc0
    @4
    cdiv
    oveq1
    eqeq1d
    syl5ibrcom
    wph
    cN
    @30
    cc0
    pceu.8
    eqeq1d
    sylibrd
    necon3d
    mpd
    #
    wph
    @11
    @31
    nnzd
    #
    @34
    cP
    cS
    cV
    @15
    vn
    @10
    @11
    pcval.1
    pceu.4
    @15
    eqid
    pcpremul
    syl122anc
    3eqtr4d
    wph
    cT
    cU
    cS
    cV
    wph
    cT
    wph
    cP
    c2
    cuz
    cfv
    wcel
    #
    @39
    @40
    cT
    cn0
    wcel
    #
    wph
    @38
    @57
    pceu.5
    cP
    prmuz2
    syl
    #
    @42
    @35
    @57
    @39
    @40
    wa
    wa
    @58
    cP
    cT
    cexp
    co
    @4
    cdvds
    wbr
    @3
    @4
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cP
    cT
    vn
    @4
    @60
    eqid
    pcval.2
    pcprecl
    simpld
    syl12anc
    nn0cnd
    wph
    cU
    wph
    @57
    @25
    @41
    cU
    cn0
    wcel
    #
    @59
    @27
    @48
    @57
    @25
    @41
    wa
    wa
    @61
    cP
    cU
    cexp
    co
    @5
    cdvds
    wbr
    @3
    @5
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cP
    cU
    vn
    @5
    @62
    eqid
    pceu.3
    pcprecl
    simpld
    syl12anc
    nn0cnd
    wph
    cS
    wph
    @57
    @21
    @49
    cS
    cn0
    wcel
    #
    @59
    @33
    @55
    @57
    @21
    @49
    wa
    wa
    @63
    cP
    cS
    cexp
    co
    @10
    cdvds
    wbr
    @3
    @10
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cP
    cS
    vn
    @10
    @64
    eqid
    pcval.1
    pcprecl
    simpld
    syl12anc
    nn0cnd
    wph
    cV
    wph
    @57
    @50
    @51
    cV
    cn0
    wcel
    #
    @59
    @56
    @34
    @57
    @50
    @51
    wa
    wa
    @65
    cP
    cV
    cexp
    co
    @11
    cdvds
    wbr
    @3
    @11
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cP
    cV
    vn
    @11
    @66
    eqid
    pceu.4
    pcprecl
    simpld
    syl12anc
    nn0cnd
    addsubeq4d
    mpbid
end
