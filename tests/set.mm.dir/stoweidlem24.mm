include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "cexp.mm"
include "clt.mm"
include "cmul.mm"
include "1red.mm"
include "cr.mm"
include "rpred.mm"
include "adantr.mm"
include "resubcld.mm"
include "nn0red.mm"
include "wf.mm"
include "c2.mm"
include "cdiv.mm"
include "wbr.mm"
include "rabeq2i.mm"
include "simplbi.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "remulcld.mm"
include "cn0.mm"
include "reexpcld.mm"
include "jca.mm"
include "nn0expcl.mm"
include "syl.mm"
include "rehalfcld.mm"
include "cc0.mm"
include "cle.mm"
include "nn0ge0d.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "sylan2.mm"
include "mulge0.mm"
include "syl12anc.mm"
include "simprbi.mm"
include "ltled.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "nn0cnd.mm"
include "rpcnd.mm"
include "2cnne0.mm"
include "a1i.mm"
include "divass.mm"
include "syl3anc.mm"
include "breqtrrd.mm"
include "leexp1a.mm"
include "syl32anc.mm"
include "lesub2dd.mm"
include "ltletrd.mm"
include "recnd.mm"
include "mulexpd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "simprd.mm"
include "exple1.mm"
include "stoweidlem10.mm"
include "eqbrtrrd.mm"
include "stoweidlem12.mm"

theorem stoweidlem24
  let wph: wff ph
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cE: class E
  let cK: class K
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem24.1: |- V = { t e. T | ( P ` t ) < ( D / 2 ) }
  assume stoweidlem24.2: |- Q = ( t e. T |-> ( ( 1 - ( ( P ` t ) ^ N ) ) ^ ( K ^ N ) ) )
  assume stoweidlem24.3: |- ( ph -> P : T --> RR )
  assume stoweidlem24.4: |- ( ph -> N e. NN0 )
  assume stoweidlem24.5: |- ( ph -> K e. NN0 )
  assume stoweidlem24.6: |- ( ph -> D e. RR+ )
  assume stoweidlem24.8: |- ( ph -> E e. RR+ )
  assume stoweidlem24.9: |- ( ph -> ( 1 - E ) < ( 1 - ( ( ( K x. D ) / 2 ) ^ N ) ) )
  assume stoweidlem24.10: |- ( ph -> A. t e. T ( 0 <_ ( P ` t ) /\ ( P ` t ) <_ 1 ) )

  disjoint T t
  disjoint k x
  assert |- ( ( ph /\ t e. V ) -> ( 1 - E ) < ( Q ` t ) )

  proof
    wph
    vt
    cv
    #
    cV
    wcel
    #
    wa
    #
    c1
    cE
    cmin
    co
    #
    c1
    @0
    cP
    cfv
    #
    cN
    cexp
    co
    #
    cmin
    co
    #
    cK
    cN
    cexp
    co
    #
    cexp
    co
    #
    @0
    cQ
    cfv
    #
    clt
    @2
    @3
    c1
    cK
    @4
    cmul
    co
    #
    cN
    cexp
    co
    #
    cmin
    co
    #
    @8
    @2
    c1
    cE
    @2
    1red
    #
    wph
    cE
    cr
    wcel
    @1
    wph
    cE
    stoweidlem24.8
    rpred
    adantr
    resubcld
    #
    @2
    c1
    @11
    @13
    @2
    @10
    cN
    @2
    cK
    @4
    wph
    cK
    cr
    wcel
    #
    @1
    wph
    cK
    stoweidlem24.5
    nn0red
    #
    adantr
    @2
    cT
    cr
    @0
    cP
    wph
    cT
    cr
    cP
    wf
    @1
    stoweidlem24.3
    adantr
    @1
    @0
    cT
    wcel
    #
    wph
    @1
    @17
    @4
    cD
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @19
    vt
    cV
    cT
    stoweidlem24.1
    rabeq2i
    #
    simplbi
    #
    adantl
    ffvelrnd
    #
    remulcld
    #
    wph
    cN
    cn0
    wcel
    #
    @1
    stoweidlem24.4
    adantr
    #
    reexpcld
    #
    resubcld
    #
    @2
    @6
    @7
    @2
    c1
    @5
    @13
    @2
    @4
    cN
    @22
    @25
    reexpcld
    #
    resubcld
    @2
    cK
    cn0
    wcel
    #
    @24
    wa
    #
    @7
    cn0
    wcel
    #
    wph
    @30
    @1
    wph
    @29
    @24
    stoweidlem24.5
    stoweidlem24.4
    jca
    adantr
    cK
    cN
    nn0expcl
    syl
    #
    reexpcld
    @2
    @3
    c1
    cK
    cD
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cN
    cexp
    co
    #
    cmin
    co
    #
    @12
    @14
    wph
    @36
    cr
    wcel
    @1
    wph
    c1
    @35
    wph
    1red
    wph
    @34
    cN
    wph
    @33
    wph
    cK
    cD
    @16
    wph
    cD
    stoweidlem24.6
    rpred
    #
    remulcld
    rehalfcld
    #
    stoweidlem24.4
    reexpcld
    #
    resubcld
    adantr
    @27
    wph
    @3
    @36
    clt
    wbr
    @1
    stoweidlem24.9
    adantr
    @2
    @11
    @35
    c1
    @26
    wph
    @35
    cr
    wcel
    @1
    @39
    adantr
    @13
    @2
    @10
    cr
    wcel
    @34
    cr
    wcel
    #
    @24
    cc0
    @10
    cle
    wbr
    #
    @10
    @34
    cle
    wbr
    @11
    @35
    cle
    wbr
    @23
    wph
    @40
    @1
    @38
    adantr
    @25
    @2
    @15
    cc0
    cK
    cle
    wbr
    #
    wa
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @41
    wph
    @43
    @1
    wph
    @15
    @42
    @16
    wph
    cK
    stoweidlem24.5
    nn0ge0d
    jca
    adantr
    #
    @22
    @1
    wph
    @17
    @45
    @21
    wph
    @17
    wa
    @45
    @4
    c1
    cle
    wbr
    #
    wph
    @45
    @47
    wa
    #
    vt
    cT
    stoweidlem24.10
    r19.21bi
    #
    simpld
    sylan2
    #
    cK
    @4
    mulge0
    syl12anc
    @2
    @10
    cK
    @18
    cmul
    co
    #
    @34
    cle
    @2
    @44
    @18
    cr
    wcel
    #
    @43
    @4
    @18
    cle
    wbr
    @10
    @51
    cle
    wbr
    @22
    wph
    @52
    @1
    wph
    cD
    @37
    rehalfcld
    adantr
    #
    @46
    @2
    @4
    @18
    @22
    @53
    @1
    @19
    wph
    @1
    @17
    @19
    @20
    simprbi
    adantl
    ltled
    @4
    @18
    cK
    lemul2a
    syl31anc
    @2
    cK
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @34
    @51
    wceq
    wph
    @54
    @1
    wph
    cK
    stoweidlem24.5
    nn0cnd
    adantr
    #
    wph
    @55
    @1
    wph
    cD
    stoweidlem24.6
    rpcnd
    adantr
    @56
    @2
    2cnne0
    a1i
    cK
    cD
    c2
    divass
    syl3anc
    breqtrrd
    @10
    @34
    cN
    leexp1a
    syl32anc
    lesub2dd
    ltletrd
    @2
    c1
    @7
    @5
    cmul
    co
    #
    cmin
    co
    #
    @12
    @8
    cle
    @2
    @58
    @11
    c1
    cmin
    @2
    @11
    @58
    @2
    cK
    @4
    cN
    @57
    @2
    @4
    @22
    recnd
    @25
    mulexpd
    eqcomd
    oveq2d
    @2
    @5
    cr
    wcel
    @31
    @5
    c1
    cle
    wbr
    #
    @59
    @8
    cle
    wbr
    @28
    @32
    @2
    @44
    @45
    @47
    @24
    @60
    @22
    @50
    @2
    @45
    @47
    @1
    wph
    @17
    @48
    @21
    @49
    sylan2
    simprd
    @25
    @4
    cN
    exple1
    syl31anc
    @5
    @7
    stoweidlem10
    syl3anc
    eqbrtrrd
    ltletrd
    @1
    wph
    @17
    @9
    @8
    wceq
    @21
    wph
    vt
    cP
    cQ
    cT
    cK
    cN
    stoweidlem24.2
    stoweidlem24.3
    stoweidlem24.4
    stoweidlem24.5
    stoweidlem12
    sylan2
    breqtrrd
end
