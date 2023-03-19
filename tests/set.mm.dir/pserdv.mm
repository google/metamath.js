include "cc.mm"
include "cdv.mm"
include "co.mm"
include "cn0.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cfv.mm"
include "cmul.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt.mm"
include "cdm.mm"
include "wf.mm"
include "dvfcn.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "ccncf.mm"
include "wcel.mm"
include "psercn.mm"
include "cncff.mm"
include "syl.mm"
include "cabs.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "dvbss.mm"
include "wa.mm"
include "cres.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cnt.mm"
include "wceq.mm"
include "adantr.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "0cnd.mm"
include "sselda.mm"
include "abscld.mm"
include "crp.mm"
include "clt.mm"
include "wbr.mm"
include "psercnlem1.mm"
include "simp1d.mm"
include "rpred.mm"
include "readdcld.mm"
include "0red.mm"
include "absge0d.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "rphalfcld.mm"
include "rpxrd.mm"
include "blssm.mm"
include "syl3anc.mm"
include "syl5eqss.mm"
include "eqid.mm"
include "crest.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "dvres.mm"
include "syl22anc.mm"
include "resss.mm"
include "syl6eqss.mm"
include "dmss.mm"
include "cicc.mm"
include "pserdvlem1.mm"
include "psercnlem2.mm"
include "syl6eleqr.mm"
include "pserdvlem2.mm"
include "dmeqd.mm"
include "cvv.mm"
include "dmmptg.mm"
include "sumex.mm"
include "mprg.mm"
include "syl6eq.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "mpbii.mm"
include "feqmptd.mm"
include "wfun.mm"
include "ffun.mm"
include "mp1i.mm"
include "funssfv.mm"
include "fveq1d.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "fvmpt.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cbvmptv.mm"

theorem pserdv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vi: setvar i
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume psercn.s: |- S = ( `' abs " ( 0 [,) R ) )
  assume psercn.m: |- M = if ( R e. RR , ( ( ( abs ` a ) + R ) / 2 ) , ( ( abs ` a ) + 1 ) )
  assume pserdv.b: |- B = ( 0 ( ball ` ( abs o. - ) ) ( ( ( abs ` a ) + M ) / 2 ) )

  disjoint A n
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint M j
  disjoint M k
  disjoint M y
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint G j
  disjoint G k
  disjoint G r
  disjoint G y
  disjoint S a
  disjoint S j
  disjoint S k
  disjoint S y
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint i n
  disjoint A i
  disjoint a m
  disjoint a s
  disjoint a w
  disjoint a z
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k s
  disjoint k w
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint M i
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint i x
  disjoint B i
  disjoint B m
  disjoint B z
  disjoint i r
  disjoint G i
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S i
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F f
  disjoint F z
  disjoint f ph
  disjoint i ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ph -> ( CC _D F ) = ( y e. S |-> sum_ k e. NN0 ( ( ( k + 1 ) x. ( A ` ( k + 1 ) ) ) x. ( y ^ k ) ) ) )

  proof
    wph
    cc
    cF
    cdv
    co
    #
    va
    cS
    cn0
    vk
    cv
    #
    c1
    caddc
    co
    #
    @2
    cA
    cfv
    cmul
    co
    #
    va
    cv
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    vy
    cS
    cn0
    @3
    vy
    cv
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    wph
    @0
    va
    cS
    @4
    @0
    cfv
    #
    cmpt
    @8
    wph
    va
    cS
    cc
    @0
    wph
    @0
    cdm
    #
    cc
    @0
    wf
    #
    cS
    cc
    @0
    wf
    cF
    dvfcn
    #
    wph
    @14
    cS
    cc
    @0
    wph
    @14
    cS
    wph
    cS
    cc
    cF
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    wph
    cF
    cS
    cc
    ccncf
    co
    wcel
    cS
    cc
    cF
    wf
    #
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    psercn
    cS
    cc
    cF
    cncff
    syl
    #
    cS
    cc
    wss
    #
    wph
    cS
    cabs
    ccnv
    #
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc
    psercn.s
    @24
    cabs
    cdm
    cc
    cabs
    @23
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    eqsstri
    #
    a1i
    #
    dvbss
    wph
    va
    cS
    @14
    wph
    @4
    cS
    wcel
    #
    @4
    @14
    wcel
    wph
    @27
    wa
    #
    cc
    cF
    cB
    cres
    cdv
    co
    #
    cdm
    #
    @14
    @4
    @28
    @29
    @0
    wss
    #
    @30
    @14
    wss
    @28
    @29
    @0
    cB
    ccnfld
    ctopn
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @0
    @28
    @17
    @19
    @21
    cB
    cc
    wss
    @29
    @34
    wceq
    @17
    @28
    @18
    a1i
    wph
    @19
    @27
    @20
    adantr
    @21
    @28
    @25
    a1i
    @28
    cB
    cc0
    @4
    cabs
    cfv
    #
    cM
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cc
    pserdv.b
    @28
    @38
    cc
    cxmt
    cfv
    wcel
    #
    cc0
    cc
    wcel
    @37
    cxr
    wcel
    @39
    cc
    wss
    @40
    @28
    cnxmet
    a1i
    @28
    0cnd
    @28
    @37
    @28
    @36
    @28
    @36
    @28
    @35
    cM
    @28
    @4
    wph
    cS
    cc
    @4
    @26
    sselda
    #
    abscld
    #
    @28
    cM
    @28
    cM
    crp
    wcel
    @35
    cM
    clt
    wbr
    cM
    cR
    clt
    wbr
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    psercnlem1
    simp1d
    #
    rpred
    readdcld
    #
    @28
    cc0
    @35
    @36
    @28
    0red
    @42
    @44
    @28
    @4
    @41
    absge0d
    @28
    @35
    cM
    @42
    @43
    ltaddrpd
    lelttrd
    elrpd
    rphalfcld
    rpxrd
    @38
    cc0
    @37
    cc
    blssm
    syl3anc
    syl5eqss
    cS
    cB
    cc
    @32
    cF
    @32
    @32
    eqid
    #
    @32
    cc
    crest
    co
    #
    @32
    @32
    ctop
    wcel
    @46
    @32
    wceq
    @32
    @45
    cnfldtop
    @32
    ctop
    cc
    cc
    @32
    @32
    @45
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    dvres
    syl22anc
    @0
    @33
    resss
    syl6eqss
    #
    @29
    @0
    dmss
    syl
    @28
    @4
    cB
    @30
    @28
    @4
    @39
    cB
    @28
    @4
    @39
    wcel
    @39
    @22
    cc0
    @37
    cicc
    co
    cima
    #
    wss
    @48
    cS
    wss
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    @37
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    pserdvlem1
    psercnlem2
    simp1d
    pserdv.b
    syl6eleqr
    #
    @28
    @30
    vy
    cB
    @12
    cmpt
    #
    cdm
    #
    cB
    @28
    @29
    @50
    wph
    vx
    vy
    cA
    cB
    cR
    cS
    vj
    vk
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    pserdv.b
    pserdvlem2
    #
    dmeqd
    @12
    cvv
    wcel
    #
    @51
    cB
    wceq
    vy
    cB
    vy
    cB
    @12
    cvv
    dmmptg
    @53
    @9
    cB
    wcel
    cn0
    @11
    vk
    sumex
    a1i
    mprg
    syl6eq
    eleqtrrd
    #
    sseldd
    ex
    ssrdv
    eqssd
    feq2d
    mpbii
    feqmptd
    wph
    va
    cS
    @13
    @7
    @28
    @13
    @4
    @29
    cfv
    #
    @4
    @50
    cfv
    #
    @7
    @28
    @0
    wfun
    #
    @31
    @4
    @30
    wcel
    @13
    @55
    wceq
    @15
    @57
    @28
    @16
    @14
    cc
    @0
    ffun
    mp1i
    @47
    @54
    @4
    @0
    @29
    funssfv
    syl3anc
    @28
    @4
    @29
    @50
    @52
    fveq1d
    @28
    @4
    cB
    wcel
    @56
    @7
    wceq
    @49
    vy
    @4
    @12
    @7
    cB
    @50
    vy
    va
    weq
    #
    cn0
    @11
    @6
    vk
    @58
    @10
    @5
    @3
    cmul
    @9
    @4
    @1
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    @50
    eqid
    cn0
    @6
    vk
    sumex
    fvmpt
    syl
    3eqtrd
    mpteq2dva
    eqtrd
    va
    vy
    cS
    @7
    @12
    va
    vy
    weq
    #
    cn0
    @6
    @11
    vk
    @59
    @5
    @10
    @3
    cmul
    @4
    @9
    @1
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    cbvmptv
    syl6eq
end
