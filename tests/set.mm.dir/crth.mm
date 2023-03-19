include "wf1.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cmo.mm"
include "co.mm"
include "cop.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "cmul.mm"
include "cfzo.mm"
include "elfzoelz.mm"
include "eleq2s.mm"
include "wa.mm"
include "cxp.mm"
include "cn.mm"
include "simpr.mm"
include "cgcd.mm"
include "c1.mm"
include "simp1d.mm"
include "adantr.mm"
include "zmodfzo.mm"
include "syl2anc.mm"
include "simp2d.mm"
include "opelxpi.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "fmptd.mm"
include "oveq1.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "ovex.mm"
include "opth.mm"
include "syl6bb.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "nnzd.mm"
include "simprl.mm"
include "syl6eleq.mm"
include "syl.mm"
include "simprr.mm"
include "zsubcld.mm"
include "simp3d.mm"
include "coprmdvds2.mm"
include "syl31anc.mm"
include "wb.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "anbi12d.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "clt.mm"
include "zred.mm"
include "nnmulcld.mm"
include "nnrpd.mm"
include "elfzole1.mm"
include "elfzolt2.mm"
include "modid.mm"
include "syl22anc.mm"
include "bitr3d.mm"
include "3imtr4d.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "cen.mm"
include "cfn.mm"
include "cn0.mm"
include "nnnn0.mm"
include "chash.mm"
include "nn0mulcl.mm"
include "hashfzo0.mm"
include "fzofi.mm"
include "hashxp.mm"
include "mp2an.mm"
include "oveqan12d.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "xpfi.mm"
include "hashen.mm"
include "sylib.mm"
include "syl2an.mm"
include "3brtr4g.mm"
include "eqeltri.mm"
include "f1finf1o.mm"
include "sylancl.mm"
include "mpbid.mm"

theorem crth
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cF: class F
  let cM: class M
  let cN: class N
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cV: class V
  let cW: class W
  assume crth.1: |- S = ( 0 ..^ ( M x. N ) )
  assume crth.2: |- T = ( ( 0 ..^ M ) X. ( 0 ..^ N ) )
  assume crth.3: |- F = ( x e. S |-> <. ( x mod M ) , ( x mod N ) >. )
  assume crth.4: |- ( ph -> ( M e. NN /\ N e. NN /\ ( M gcd N ) = 1 ) )

  disjoint M x
  disjoint ph x
  disjoint S x
  disjoint T x
  disjoint N x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint w x
  disjoint M w
  disjoint x y
  disjoint M y
  disjoint ph w
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint N w
  disjoint N y
  disjoint U w
  disjoint U z
  disjoint V w
  disjoint V z
  disjoint W w
  disjoint W z
  assert |- ( ph -> F : S -1-1-onto-> T )

  proof
    wph
    cS
    cT
    cF
    wf1
    #
    cS
    cT
    cF
    wf1o
    #
    wph
    cS
    cT
    cF
    wf
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vz
    cS
    wral
    vy
    cS
    wral
    @0
    wph
    vx
    cS
    vx
    cv
    #
    cM
    cmo
    co
    #
    @9
    cN
    cmo
    co
    #
    cop
    #
    cT
    cF
    @9
    cS
    wcel
    wph
    @9
    cz
    wcel
    #
    @12
    cT
    wcel
    @13
    @9
    cc0
    cM
    cN
    cmul
    co
    #
    cfzo
    co
    #
    cS
    @9
    cc0
    @14
    elfzoelz
    crth.1
    eleq2s
    wph
    @13
    wa
    #
    @12
    cc0
    cM
    cfzo
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cxp
    #
    cT
    @16
    @10
    @17
    wcel
    #
    @11
    @18
    wcel
    #
    @12
    @19
    wcel
    @16
    @13
    cM
    cn
    wcel
    #
    @20
    wph
    @13
    simpr
    #
    wph
    @22
    @13
    wph
    @22
    cN
    cn
    wcel
    #
    cM
    cN
    cgcd
    co
    c1
    wceq
    #
    crth.4
    simp1d
    #
    adantr
    @9
    cM
    zmodfzo
    syl2anc
    @16
    @13
    @24
    @21
    @23
    wph
    @24
    @13
    wph
    @22
    @24
    @25
    crth.4
    simp2d
    #
    adantr
    @9
    cN
    zmodfzo
    syl2anc
    @10
    @11
    @17
    @18
    opelxpi
    syl2anc
    crth.2
    syl6eleqr
    sylan2
    crth.3
    fmptd
    wph
    @8
    vy
    vz
    cS
    cS
    wph
    @2
    cS
    wcel
    #
    @4
    cS
    wcel
    #
    wa
    #
    wa
    #
    @6
    @2
    cM
    cmo
    co
    #
    @4
    cM
    cmo
    co
    #
    wceq
    #
    @2
    cN
    cmo
    co
    #
    @4
    cN
    cmo
    co
    #
    wceq
    #
    wa
    #
    @7
    @31
    @6
    @32
    @35
    cop
    #
    @33
    @36
    cop
    #
    wceq
    @38
    @31
    @3
    @39
    @5
    @40
    @28
    @3
    @39
    wceq
    wph
    @29
    vx
    @2
    @12
    @39
    cS
    cF
    @9
    @2
    wceq
    @10
    @32
    @11
    @35
    @9
    @2
    cM
    cmo
    oveq1
    @9
    @2
    cN
    cmo
    oveq1
    opeq12d
    crth.3
    @32
    @35
    opex
    fvmpt
    ad2antrl
    @29
    @5
    @40
    wceq
    wph
    @28
    vx
    @4
    @12
    @40
    cS
    cF
    @9
    @4
    wceq
    @10
    @33
    @11
    @36
    @9
    @4
    cM
    cmo
    oveq1
    @9
    @4
    cN
    cmo
    oveq1
    opeq12d
    crth.3
    @33
    @36
    opex
    fvmpt
    ad2antll
    eqeq12d
    @32
    @35
    @33
    @36
    @2
    cM
    cmo
    ovex
    @2
    cN
    cmo
    ovex
    opth
    syl6bb
    @31
    cM
    @2
    @4
    cmin
    co
    #
    cdvds
    wbr
    #
    cN
    @41
    cdvds
    wbr
    #
    wa
    #
    @14
    @41
    cdvds
    wbr
    #
    @38
    @7
    @31
    cM
    cz
    wcel
    cN
    cz
    wcel
    @41
    cz
    wcel
    @25
    @44
    @45
    wi
    @31
    cM
    wph
    @22
    @30
    @26
    adantr
    #
    nnzd
    @31
    cN
    wph
    @24
    @30
    @27
    adantr
    #
    nnzd
    @31
    @2
    @4
    @31
    @2
    @15
    wcel
    #
    @2
    cz
    wcel
    #
    @31
    @2
    cS
    @15
    wph
    @28
    @29
    simprl
    crth.1
    syl6eleq
    #
    @2
    cc0
    @14
    elfzoelz
    syl
    #
    @31
    @4
    @15
    wcel
    #
    @4
    cz
    wcel
    #
    @31
    @4
    cS
    @15
    wph
    @28
    @29
    simprr
    crth.1
    syl6eleq
    #
    @4
    cc0
    @14
    elfzoelz
    syl
    #
    zsubcld
    wph
    @25
    @30
    wph
    @22
    @24
    @25
    crth.4
    simp3d
    adantr
    @41
    cM
    cN
    coprmdvds2
    syl31anc
    @31
    @34
    @42
    @37
    @43
    @31
    @22
    @49
    @53
    @34
    @42
    wb
    @46
    @51
    @55
    @2
    @4
    cM
    moddvds
    syl3anc
    @31
    @24
    @49
    @53
    @37
    @43
    wb
    @47
    @51
    @55
    @2
    @4
    cN
    moddvds
    syl3anc
    anbi12d
    @31
    @2
    @14
    cmo
    co
    #
    @4
    @14
    cmo
    co
    #
    wceq
    #
    @7
    @45
    @31
    @56
    @2
    @57
    @4
    @31
    @2
    cr
    wcel
    @14
    crp
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    @2
    @14
    clt
    wbr
    #
    @56
    @2
    wceq
    @31
    @2
    @51
    zred
    @31
    @14
    @31
    cM
    cN
    @46
    @47
    nnmulcld
    #
    nnrpd
    #
    @31
    @48
    @60
    @50
    @2
    cc0
    @14
    elfzole1
    syl
    @31
    @48
    @61
    @50
    @2
    cc0
    @14
    elfzolt2
    syl
    @2
    @14
    modid
    syl22anc
    @31
    @4
    cr
    wcel
    @59
    cc0
    @4
    cle
    wbr
    #
    @4
    @14
    clt
    wbr
    #
    @57
    @4
    wceq
    @31
    @4
    @55
    zred
    @63
    @31
    @52
    @64
    @54
    @4
    cc0
    @14
    elfzole1
    syl
    @31
    @52
    @65
    @54
    @4
    cc0
    @14
    elfzolt2
    syl
    @4
    @14
    modid
    syl22anc
    eqeq12d
    @31
    @14
    cn
    wcel
    @49
    @53
    @58
    @45
    wb
    @62
    @51
    @55
    @2
    @4
    @14
    moddvds
    syl3anc
    bitr3d
    3imtr4d
    sylbid
    ralrimivva
    vy
    vz
    cS
    cT
    cF
    dff13
    sylanbrc
    wph
    cS
    cT
    cen
    wbr
    cT
    cfn
    wcel
    @0
    @1
    wb
    wph
    @15
    @19
    cS
    cT
    cen
    wph
    @22
    @24
    @15
    @19
    cen
    wbr
    #
    @26
    @27
    @22
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @66
    @24
    cM
    nnnn0
    cN
    nnnn0
    @67
    @68
    wa
    #
    @15
    chash
    cfv
    #
    @19
    chash
    cfv
    #
    wceq
    #
    @66
    @69
    @70
    @14
    @71
    @69
    @14
    cn0
    wcel
    @70
    @14
    wceq
    cM
    cN
    nn0mulcl
    @14
    hashfzo0
    syl
    @69
    @71
    @17
    chash
    cfv
    #
    @18
    chash
    cfv
    #
    cmul
    co
    #
    @14
    @17
    cfn
    wcel
    #
    @18
    cfn
    wcel
    #
    @71
    @75
    wceq
    cc0
    cM
    fzofi
    #
    cc0
    cN
    fzofi
    #
    @17
    @18
    hashxp
    mp2an
    @67
    @68
    @73
    cM
    @74
    cN
    cmul
    cM
    hashfzo0
    cN
    hashfzo0
    oveqan12d
    syl5eq
    eqtr4d
    @15
    cfn
    wcel
    @19
    cfn
    wcel
    #
    @72
    @66
    wb
    cc0
    @14
    fzofi
    @76
    @77
    @80
    @78
    @79
    @17
    @18
    xpfi
    mp2an
    #
    @15
    @19
    hashen
    mp2an
    sylib
    syl2an
    syl2anc
    crth.1
    crth.2
    3brtr4g
    cT
    @19
    cfn
    crth.2
    @81
    eqeltri
    cS
    cT
    cF
    f1finf1o
    sylancl
    mpbid
end
