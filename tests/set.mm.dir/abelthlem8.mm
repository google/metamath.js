include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "co.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cmin.mm"
include "wi.mm"
include "wrex.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "id.mm"
include "ge0p1rpd.mm"
include "rpdivcl.mm"
include "syl2anr.mm"
include "eqidd.mm"
include "cli.mm"
include "adantr.mm"
include "climi0.mm"
include "cfz.mm"
include "csu.mm"
include "cr.mm"
include "fzfid.mm"
include "cc.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "serf.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "ad2antrr.mm"
include "cle.mm"
include "absge0d.mm"
include "fsumge0.mm"
include "rpdivcld.mm"
include "wceq.mm"
include "cneg.mm"
include "cmul.mm"
include "csn.mm"
include "cdif.mm"
include "ccom.mm"
include "cbl.mm"
include "wss.mm"
include "abelthlem2.mm"
include "simpld.mm"
include "cexp.mm"
include "oveq1.mm"
include "cz.mm"
include "nn0z.mm"
include "1exp.mm"
include "syl.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "sumex.mm"
include "fvmpt.mm"
include "mulid1d.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "isumclim.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "df-neg.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "abelthlem4.mm"
include "absnegd.mm"
include "adantlr.mm"
include "ad2ant2r.mm"
include "simplll.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "abs00bd.mm"
include "sylan.mm"
include "simpllr.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "wne.mm"
include "ad3antrrr.mm"
include "cdm.mm"
include "simprll.mm"
include "simprr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simplrl.mm"
include "simplrr.mm"
include "weq.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "simprlr.mm"
include "cbvsumv.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "syl6breq.mm"
include "abelthlem7.mm"
include "rpcn.mm"
include "adantl.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan2d.mm"
include "breqtrd.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimddv.mm"

theorem abelthlem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let cX: class X
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )
  assume abelth.7: |- ( ph -> seq 0 ( + , A ) ~~> 0 )

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint M n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint A n
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint F w
  disjoint F y
  disjoint S n
  disjoint S w
  disjoint S x
  disjoint S y
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
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint n r
  disjoint X n
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint X x
  disjoint X z
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
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S r
  assert |- ( ( ph /\ R e. RR+ ) -> E. w e. RR+ A. y e. S ( ( abs ` ( 1 - y ) ) < w -> ( abs ` ( ( F ` 1 ) - ( F ` y ) ) ) < R ) )

  proof
    wph
    cR
    crp
    wcel
    #
    wa
    #
    vk
    cv
    #
    caddc
    cA
    cc0
    cseq
    #
    cfv
    #
    cabs
    cfv
    #
    cR
    cM
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    c1
    vy
    cv
    #
    cmin
    co
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    c1
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vw
    crp
    wrex
    #
    vj
    cn0
    @1
    @4
    @7
    vj
    vk
    @3
    cc0
    cn0
    nn0uz
    @1
    0zd
    @0
    @0
    @6
    crp
    wcel
    #
    @7
    crp
    wcel
    #
    wph
    @0
    id
    wph
    cM
    abelth.3
    abelth.4
    ge0p1rpd
    #
    cR
    @6
    rpdivcl
    syl2anr
    #
    @1
    @2
    cn0
    wcel
    wa
    @4
    eqidd
    wph
    @3
    cc0
    cli
    wbr
    #
    @0
    abelth.7
    adantr
    climi0
    @1
    @9
    cn0
    wcel
    #
    @11
    wa
    #
    wa
    #
    @7
    cc0
    @9
    c1
    cmin
    co
    #
    cfz
    co
    #
    vi
    cv
    #
    @3
    cfv
    #
    cabs
    cfv
    #
    vi
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    crp
    wcel
    @13
    @39
    clt
    wbr
    #
    @20
    wi
    #
    vy
    cS
    wral
    #
    @23
    @31
    @7
    @38
    @1
    @25
    @30
    @27
    adantr
    @31
    @37
    wph
    @37
    cr
    wcel
    @0
    @30
    wph
    @33
    @36
    vi
    wph
    cc0
    @32
    fzfid
    #
    wph
    @34
    @33
    wcel
    #
    wa
    #
    @35
    wph
    cn0
    cc
    @3
    wf
    @34
    cn0
    wcel
    @35
    cc
    wcel
    @44
    wph
    vw
    cA
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    wph
    cn0
    cc
    @14
    cA
    abelth.1
    ffvelrnda
    serf
    @34
    @32
    elfznn0
    cn0
    cc
    @34
    @3
    ffvelrn
    syl2an
    #
    abscld
    #
    fsumrecl
    ad2antrr
    wph
    cc0
    @37
    cle
    wbr
    @0
    @30
    wph
    @33
    @36
    vi
    @43
    @48
    @45
    @35
    @47
    absge0d
    fsumge0
    ad2antrr
    ge0p1rpd
    rpdivcld
    @31
    @41
    vy
    cS
    @31
    @12
    cS
    wcel
    #
    @40
    @20
    @31
    @49
    @40
    wa
    #
    wa
    #
    @19
    @17
    cabs
    cfv
    #
    cR
    clt
    @1
    @49
    @19
    @52
    wceq
    #
    @30
    @40
    wph
    @49
    @53
    @0
    wph
    @49
    wa
    #
    @19
    @17
    cneg
    #
    cabs
    cfv
    @52
    @54
    @18
    @55
    cabs
    @54
    @18
    cc0
    @17
    cmin
    co
    @55
    @54
    @16
    cc0
    @17
    cmin
    wph
    @16
    cc0
    wceq
    @49
    wph
    @16
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    c1
    cmul
    co
    #
    vn
    csu
    #
    cc0
    wph
    c1
    cS
    wcel
    #
    @16
    @59
    wceq
    wph
    @60
    cS
    c1
    csn
    cdif
    #
    cc0
    c1
    cabs
    cmin
    ccom
    cbl
    cfv
    co
    wss
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
    simpld
    vx
    c1
    cn0
    @57
    vx
    cv
    #
    @56
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    @59
    cS
    cF
    @62
    c1
    wceq
    #
    cn0
    @64
    @58
    vn
    @65
    @56
    cn0
    wcel
    #
    wa
    @63
    c1
    @57
    cmul
    @65
    @66
    @63
    c1
    @56
    cexp
    co
    #
    c1
    @62
    c1
    @56
    cexp
    oveq1
    @66
    @56
    cz
    wcel
    @67
    c1
    wceq
    @56
    nn0z
    @56
    1exp
    syl
    sylan9eq
    oveq2d
    sumeq2dv
    abelth.6
    cn0
    @58
    vn
    sumex
    fvmpt
    syl
    wph
    @58
    cc0
    vn
    cA
    cc0
    cn0
    nn0uz
    @46
    wph
    @66
    wa
    #
    @58
    @57
    @68
    @57
    wph
    cn0
    cc
    @56
    cA
    abelth.1
    ffvelrnda
    #
    mulid1d
    #
    eqcomd
    @68
    @58
    @57
    cc
    @70
    @69
    eqeltrd
    abelth.7
    isumclim
    eqtrd
    #
    adantr
    oveq1d
    @17
    df-neg
    syl6eqr
    fveq2d
    @54
    @17
    wph
    cS
    cc
    @12
    cF
    wph
    vx
    vz
    cA
    cS
    vn
    cF
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelthlem4
    ffvelrnda
    absnegd
    eqtrd
    adantlr
    ad2ant2r
    @51
    @52
    cR
    clt
    wbr
    #
    @12
    c1
    @51
    @12
    c1
    wceq
    #
    wa
    @52
    cc0
    cR
    clt
    @51
    wph
    @73
    @52
    cc0
    wceq
    wph
    @0
    @30
    @50
    simplll
    wph
    @73
    wa
    @17
    @73
    wph
    @17
    @16
    cc0
    @12
    c1
    cF
    fveq2
    @71
    sylan9eqr
    abs00bd
    sylan
    @51
    cc0
    cR
    clt
    wbr
    @73
    @51
    cR
    wph
    @0
    @30
    @50
    simpllr
    rpgt0d
    adantr
    eqbrtrd
    @31
    @50
    @12
    c1
    wne
    #
    @72
    @31
    @50
    @74
    wa
    #
    wa
    #
    @52
    @6
    @7
    cmul
    co
    #
    cR
    clt
    @76
    vx
    vz
    cA
    @7
    cS
    vm
    vn
    cF
    cM
    @9
    @12
    wph
    cn0
    cc
    cA
    wf
    @0
    @30
    @75
    abelth.1
    ad3antrrr
    wph
    @3
    cli
    cdm
    wcel
    @0
    @30
    @75
    abelth.2
    ad3antrrr
    wph
    cM
    cr
    wcel
    @0
    @30
    @75
    abelth.3
    ad3antrrr
    wph
    cc0
    cM
    cle
    wbr
    @0
    @30
    @75
    abelth.4
    ad3antrrr
    abelth.5
    abelth.6
    wph
    @28
    @0
    @30
    @75
    abelth.7
    ad3antrrr
    @76
    @49
    @74
    @12
    @61
    wcel
    @31
    @49
    @40
    @74
    simprll
    @31
    @50
    @74
    simprr
    @12
    cS
    c1
    eldifsn
    sylanbrc
    @1
    @25
    @30
    @75
    @27
    ad2antrr
    @1
    @29
    @11
    @75
    simplrl
    @76
    @11
    vm
    cv
    #
    @3
    cfv
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    vm
    @10
    wral
    @1
    @29
    @11
    @75
    simplrr
    @8
    @81
    vk
    vm
    @10
    vk
    vm
    weq
    #
    @5
    @80
    @7
    clt
    @82
    @4
    @79
    cabs
    @2
    @78
    @3
    fveq2
    fveq2d
    breq1d
    cbvralv
    sylib
    @76
    @13
    @39
    @7
    @33
    @56
    @3
    cfv
    #
    cabs
    cfv
    #
    vn
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    clt
    @31
    @49
    @40
    @74
    simprlr
    @38
    @86
    @7
    cdiv
    @37
    @85
    c1
    caddc
    @33
    @36
    @84
    vi
    vn
    vi
    vn
    weq
    @35
    @83
    cabs
    @34
    @56
    @3
    fveq2
    fveq2d
    cbvsumv
    oveq1i
    oveq2i
    syl6breq
    abelthlem7
    @1
    @77
    cR
    wceq
    @30
    @75
    @1
    cR
    @6
    @0
    cR
    cc
    wcel
    wph
    cR
    rpcn
    adantl
    @1
    @6
    wph
    @24
    @0
    @26
    adantr
    #
    rpcnd
    @1
    @6
    @87
    rpne0d
    divcan2d
    ad2antrr
    breqtrd
    anassrs
    pm2.61dane
    eqbrtrd
    expr
    ralrimiva
    @22
    @42
    vw
    @39
    crp
    @14
    @39
    wceq
    #
    @21
    @41
    vy
    cS
    @88
    @15
    @40
    @20
    @14
    @39
    @13
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rexlimddv
end
