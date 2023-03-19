include "cc0.mm"
include "c1.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "cseq.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn0.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "cli.mm"
include "cdm.mm"
include "wrex.mm"
include "nn0uz.mm"
include "0zd.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "eqidd.mm"
include "climi0.mm"
include "adantr.mm"
include "simprl.mm"
include "cr.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cc.mm"
include "cxmt.mm"
include "cxr.mm"
include "wss.mm"
include "cnxmet.mm"
include "0cn.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "blssm.mm"
include "mp3an.mm"
include "simplr.mm"
include "sseldi.mm"
include "abscld.mm"
include "reexpcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "serf.mm"
include "ad2antrr.mm"
include "expcl.mm"
include "mulcld.mm"
include "cdiv.mm"
include "recnd.mm"
include "absidm.mm"
include "syl.mm"
include "cnmetdval.mm"
include "sylancl.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "wb.mm"
include "elbl3.mm"
include "mpanl12.mm"
include "sylancr.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "eqbrtrd.mm"
include "geolim.mm"
include "climrel.mm"
include "releldmi.mm"
include "1red.mm"
include "cle.mm"
include "eluznn0.mm"
include "ffvelrnd.mm"
include "syldan.mm"
include "absmuld.mm"
include "absexpd.mm"
include "oveq2d.mm"
include "absge0d.mm"
include "breqtrd.mm"
include "simprr.mm"
include "breq1d.mm"
include "rspccva.mm"
include "wi.mm"
include "1re.mm"
include "ltle.mm"
include "mpd.mm"
include "lemul1ad.mm"
include "3brtr4d.mm"
include "cvgcmpce.mm"
include "rexlimddv.mm"

theorem abelthlem5
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let cR: class R
  let vr: setvar r
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

  disjoint k n
  disjoint k x
  disjoint k z
  disjoint M k
  disjoint n x
  disjoint n z
  disjoint M n
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint X k
  disjoint X n
  disjoint X x
  disjoint X z
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint A z
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint S k
  disjoint S n
  disjoint S x
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
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint y z
  disjoint M y
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint n r
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
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
  disjoint A w
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S m
  disjoint S r
  disjoint S w
  disjoint S y
  assert |- ( ( ph /\ X e. ( 0 ( ball ` ( abs o. - ) ) 1 ) ) -> seq 0 ( + , ( k e. NN0 |-> ( ( seq 0 ( + , A ) ` k ) x. ( X ^ k ) ) ) ) e. dom ~~> )

  proof
    wph
    cX
    cc0
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    wcel
    #
    wa
    #
    vm
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
    c1
    clt
    wbr
    #
    vm
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    caddc
    vk
    cn0
    vk
    cv
    #
    @5
    cfv
    #
    cX
    @12
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    cli
    cdm
    #
    wcel
    vj
    cn0
    wph
    @11
    vj
    cn0
    wrex
    @2
    wph
    @6
    c1
    vj
    vm
    @5
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    c1
    crp
    wcel
    #
    wph
    1rp
    a1i
    wph
    @4
    cn0
    wcel
    wa
    @6
    eqidd
    abelth.7
    climi0
    adantr
    @3
    @9
    cn0
    wcel
    #
    @11
    wa
    #
    wa
    #
    c1
    vi
    vn
    cn0
    cX
    cabs
    cfv
    #
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    @16
    cc0
    @9
    cn0
    nn0uz
    @3
    @20
    @11
    simprl
    #
    @22
    vi
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @28
    @26
    cfv
    #
    @23
    @28
    cexp
    co
    #
    cr
    @29
    @31
    @32
    wceq
    #
    @22
    vn
    @28
    @25
    @32
    cn0
    @26
    @24
    @28
    @23
    cexp
    oveq2
    @26
    eqid
    @23
    @28
    cexp
    ovex
    fvmpt
    #
    adantl
    #
    @22
    @23
    cr
    wcel
    @29
    @32
    cr
    wcel
    #
    @22
    cX
    @22
    @1
    cc
    cX
    @0
    cc
    cxmt
    cfv
    wcel
    #
    cc0
    cc
    wcel
    #
    c1
    cxr
    wcel
    #
    @1
    cc
    wss
    cnxmet
    0cn
    @19
    @39
    1rp
    c1
    rpxr
    ax-mp
    #
    @0
    cc0
    c1
    cc
    blssm
    mp3an
    wph
    @2
    @21
    simplr
    #
    sseldi
    #
    abscld
    #
    @23
    @28
    reexpcl
    sylan
    #
    eqeltrd
    @30
    @28
    @16
    cfv
    #
    @28
    @5
    cfv
    #
    cX
    @28
    cexp
    co
    #
    cmul
    co
    #
    cc
    @29
    @45
    @48
    wceq
    #
    @22
    vk
    @28
    @15
    @48
    cn0
    @16
    vk
    vi
    weq
    @13
    @46
    @14
    @47
    cmul
    @12
    @28
    @5
    fveq2
    @12
    @28
    cX
    cexp
    oveq2
    oveq12d
    @16
    eqid
    @46
    @47
    cmul
    ovex
    fvmpt
    #
    adantl
    @30
    @46
    @47
    @22
    cn0
    cc
    @28
    @5
    wph
    cn0
    cc
    @5
    wf
    #
    @2
    @21
    wph
    vx
    cA
    cc0
    cn0
    nn0uz
    @18
    wph
    cn0
    cc
    vx
    cv
    cA
    abelth.1
    ffvelrnda
    serf
    ad2antrr
    #
    ffvelrnda
    @22
    cX
    cc
    wcel
    #
    @29
    @47
    cc
    wcel
    #
    @42
    cX
    @28
    expcl
    sylan
    #
    mulcld
    eqeltrd
    @22
    caddc
    @26
    cc0
    cseq
    #
    c1
    c1
    @23
    cmin
    co
    cdiv
    co
    #
    cli
    wbr
    @56
    @17
    wcel
    @22
    @23
    vi
    @26
    @22
    @23
    @43
    recnd
    @22
    @23
    cabs
    cfv
    #
    @23
    c1
    clt
    @22
    @53
    @58
    @23
    wceq
    @42
    cX
    absidm
    syl
    @22
    cX
    cc0
    @0
    co
    #
    @23
    c1
    clt
    @22
    @59
    cX
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @23
    @22
    @53
    @38
    @59
    @61
    wceq
    @42
    0cn
    cX
    cc0
    @0
    @0
    eqid
    cnmetdval
    sylancl
    @22
    @60
    cX
    cabs
    @22
    cX
    @42
    subid1d
    fveq2d
    eqtrd
    @22
    @2
    @59
    c1
    clt
    wbr
    #
    @41
    @22
    @38
    @53
    @2
    @62
    wb
    #
    0cn
    @42
    @37
    @39
    @38
    @53
    wa
    @63
    cnxmet
    @40
    cX
    @0
    cc0
    c1
    cc
    elbl3
    mpanl12
    sylancr
    mpbid
    eqbrtrrd
    eqbrtrd
    @35
    geolim
    @56
    @57
    cli
    climrel
    releldmi
    syl
    @22
    1red
    @22
    @28
    @10
    wcel
    #
    wa
    #
    @48
    cabs
    cfv
    #
    c1
    @32
    cmul
    co
    #
    @45
    cabs
    cfv
    c1
    @31
    cmul
    co
    cle
    @65
    @66
    @46
    cabs
    cfv
    #
    @32
    cmul
    co
    #
    @67
    cle
    @65
    @66
    @68
    @47
    cabs
    cfv
    #
    cmul
    co
    @69
    @65
    @46
    @47
    @65
    cn0
    cc
    @28
    @5
    @22
    @51
    @64
    @52
    adantr
    @22
    @20
    @64
    @29
    @27
    @28
    @9
    eluznn0
    sylan
    #
    ffvelrnd
    #
    @22
    @64
    @29
    @54
    @71
    @55
    syldan
    #
    absmuld
    @65
    @70
    @32
    @68
    cmul
    @65
    cX
    @28
    @22
    @53
    @64
    @42
    adantr
    @71
    absexpd
    #
    oveq2d
    eqtrd
    @65
    @68
    c1
    @32
    @65
    @46
    @72
    abscld
    #
    @65
    1red
    @22
    @64
    @29
    @36
    @71
    @44
    syldan
    @65
    cc0
    @70
    @32
    cle
    @65
    @47
    @73
    absge0d
    @74
    breqtrd
    @65
    @68
    c1
    clt
    wbr
    #
    @68
    c1
    cle
    wbr
    #
    @22
    @11
    @64
    @76
    @3
    @20
    @11
    simprr
    @8
    @76
    vm
    @28
    @10
    vm
    vi
    weq
    #
    @7
    @68
    c1
    clt
    @78
    @6
    @46
    cabs
    @4
    @28
    @5
    fveq2
    fveq2d
    breq1d
    rspccva
    sylan
    @65
    @68
    cr
    wcel
    c1
    cr
    wcel
    @76
    @77
    wi
    @75
    1re
    @68
    c1
    ltle
    sylancl
    mpd
    lemul1ad
    eqbrtrd
    @65
    @45
    @48
    cabs
    @65
    @29
    @49
    @71
    @50
    syl
    fveq2d
    @65
    @31
    @32
    c1
    cmul
    @65
    @29
    @33
    @71
    @34
    syl
    oveq2d
    3brtr4d
    cvgcmpce
    rexlimddv
end
