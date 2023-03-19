include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cmul.mm"
include "cmin.mm"
include "citg.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "cioo.mm"
include "wral.mm"
include "wrex.mm"
include "caddc.mm"
include "c1.mm"
include "cfl.mm"
include "cz.mm"
include "cc0.mm"
include "cr.mm"
include "abscld.mm"
include "syl5eqel.mm"
include "readdcld.mm"
include "wa.mm"
include "cc.mm"
include "iblabs.mm"
include "itgrecl.mm"
include "rpred.mm"
include "rpne0d.mm"
include "redivcld.mm"
include "1red.mm"
include "flcld.mm"
include "0red.mm"
include "reflcl.mm"
include "syl.mm"
include "0lt1.mm"
include "a1i.mm"
include "cle.mm"
include "cn0.mm"
include "absge0d.mm"
include "syl6breqr.mm"
include "addge0d.mm"
include "itgge0.mm"
include "divge0d.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0addge1.mm"
include "wceq.mm"
include "1z.mm"
include "fladdz.mm"
include "sylancl.mm"
include "nn0cnd.mm"
include "recnd.mm"
include "addcomd.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "ltletrd.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "peano2nnd.mm"
include "cmpt.mm"
include "cibl.mm"
include "elioore.mm"
include "sylan2.mm"
include "adantlr.mm"
include "simpll.mm"
include "simpr.mm"
include "ad2antlr.mm"
include "syl21anc.mm"
include "adantr.mm"
include "eqid.mm"
include "crp.mm"
include "adantl.mm"
include "eqcomi.mm"
include "oveq12i.mm"
include "oveq1i.mm"
include "negcld.mm"
include "mulcld.mm"
include "itgcl.mm"
include "syl5eqelr.mm"
include "wne.mm"
include "itgabs.mm"
include "absmuld.mm"
include "recn.mm"
include "absnegd.mm"
include "eqbrtrd.mm"
include "lemul2ad.mm"
include "mulid1d.mm"
include "itgle.mm"
include "letrd.mm"
include "leadd2dd.mm"
include "lediv1dd.mm"
include "flltp1.mm"
include "breqtrrd.mm"
include "lelttrd.mm"
include "ltadd1dd.mm"
include "cxr.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "lttrd.mm"
include "ltled.mm"
include "syldan.mm"
include "fourierdlem30.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "rspcev.mm"

theorem fourierdlem47
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vr: setvar r
  let vk: setvar k
  assume fourierdlem47.ibl: |- ( ph -> ( x e. I |-> F ) e. L^1 )
  assume fourierdlem47.iblmul: |- ( ( ph /\ r e. RR ) -> ( x e. I |-> ( F x. -u G ) ) e. L^1 )
  assume fourierdlem47.f: |- ( ( ph /\ x e. I ) -> F e. CC )
  assume fourierdlem47.g: |- ( ( ( ph /\ x e. I ) /\ r e. CC ) -> G e. CC )
  assume fourierdlem47.absg: |- ( ( ( ph /\ x e. I ) /\ r e. RR ) -> ( abs ` G ) <_ 1 )
  assume fourierdlem47.a: |- ( ph -> A e. CC )
  assume fourierdlem47.x: |- X = ( abs ` A )
  assume fourierdlem47.c: |- ( ph -> C e. CC )
  assume fourierdlem47.y: |- Y = ( abs ` C )
  assume fourierdlem47.z: |- Z = S. I ( abs ` F ) _d x
  assume fourierdlem47.e: |- ( ph -> E e. RR+ )
  assume fourierdlem47.b: |- ( ( ph /\ r e. CC ) -> B e. CC )
  assume fourierdlem47.absb: |- ( ( ph /\ r e. RR ) -> ( abs ` B ) <_ 1 )
  assume fourierdlem47.d: |- ( ( ph /\ r e. CC ) -> D e. CC )
  assume fourierdlem47.absd: |- ( ( ph /\ r e. RR ) -> ( abs ` D ) <_ 1 )
  assume fourierdlem47.m: |- M = ( ( |_ ` ( ( ( ( X + Y ) + Z ) / E ) + 1 ) ) + 1 )

  disjoint A m
  disjoint B m
  disjoint C m
  disjoint D m
  disjoint E m
  disjoint F m
  disjoint G m
  disjoint I m
  disjoint I x
  disjoint m x
  disjoint M m
  disjoint M r
  disjoint M x
  disjoint m r
  disjoint r x
  disjoint ph r
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. m e. NN A. r e. ( m (,) +oo ) ( abs ` ( ( ( A x. -u ( B / r ) ) - ( C x. -u ( D / r ) ) ) - S. I ( F x. -u ( G / r ) ) _d x ) ) < E )

  proof
    wph
    cM
    cn
    wcel
    cA
    cB
    vr
    cv
    #
    cdiv
    co
    cneg
    cmul
    co
    cC
    cD
    @0
    cdiv
    co
    cneg
    cmul
    co
    cmin
    co
    vx
    cI
    cF
    cG
    @0
    cdiv
    co
    cneg
    cmul
    co
    citg
    cmin
    co
    cabs
    cfv
    cE
    clt
    wbr
    #
    vr
    cM
    cpnf
    cioo
    co
    #
    wral
    #
    @1
    vr
    vm
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vm
    cn
    wrex
    wph
    cM
    cX
    cY
    caddc
    co
    #
    cZ
    caddc
    co
    #
    cE
    cdiv
    co
    #
    c1
    caddc
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    fourierdlem47.m
    wph
    @11
    wph
    @11
    cz
    wcel
    cc0
    @11
    clt
    wbr
    @11
    cn
    wcel
    wph
    @10
    wph
    @9
    c1
    wph
    @8
    cE
    wph
    @7
    cZ
    wph
    cX
    cY
    wph
    cX
    cA
    cabs
    cfv
    #
    cr
    fourierdlem47.x
    wph
    cA
    fourierdlem47.a
    abscld
    #
    syl5eqel
    #
    wph
    cY
    cC
    cabs
    cfv
    #
    cr
    fourierdlem47.y
    wph
    cC
    fourierdlem47.c
    abscld
    #
    syl5eqel
    #
    readdcld
    #
    wph
    cZ
    vx
    cI
    cF
    cabs
    cfv
    #
    citg
    #
    cr
    fourierdlem47.z
    wph
    vx
    cI
    @20
    wph
    vx
    cv
    cI
    wcel
    #
    wa
    #
    cF
    fourierdlem47.f
    abscld
    #
    wph
    vx
    cI
    cF
    cc
    fourierdlem47.f
    fourierdlem47.ibl
    iblabs
    #
    itgrecl
    syl5eqel
    #
    readdcld
    #
    wph
    cE
    fourierdlem47.e
    rpred
    #
    wph
    cE
    fourierdlem47.e
    rpne0d
    #
    redivcld
    #
    wph
    1red
    #
    readdcld
    #
    flcld
    wph
    cc0
    c1
    @11
    wph
    0red
    @31
    wph
    @10
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @32
    @10
    reflcl
    #
    syl
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    c1
    c1
    @9
    cfl
    cfv
    #
    caddc
    co
    #
    @11
    cle
    wph
    c1
    cr
    wcel
    @36
    cn0
    wcel
    #
    c1
    @37
    cle
    wbr
    @31
    wph
    @9
    cr
    wcel
    #
    cc0
    @9
    cle
    wbr
    @38
    @30
    wph
    @8
    cE
    @27
    fourierdlem47.e
    wph
    @7
    cZ
    @19
    @26
    wph
    cX
    cY
    @15
    @18
    wph
    cc0
    @13
    cX
    cle
    wph
    cA
    fourierdlem47.a
    absge0d
    fourierdlem47.x
    syl6breqr
    wph
    cc0
    @16
    cY
    cle
    wph
    cC
    fourierdlem47.c
    absge0d
    fourierdlem47.y
    syl6breqr
    addge0d
    wph
    cc0
    @21
    cZ
    cle
    wph
    vx
    cI
    @20
    @25
    @24
    @23
    cF
    fourierdlem47.f
    absge0d
    itgge0
    fourierdlem47.z
    syl6breqr
    addge0d
    divge0d
    @9
    flge0nn0
    syl2anc
    #
    c1
    @36
    nn0addge1
    syl2anc
    wph
    @11
    @36
    c1
    caddc
    co
    #
    @37
    wph
    @39
    c1
    cz
    wcel
    #
    @11
    @41
    wceq
    #
    @30
    1z
    @9
    c1
    fladdz
    #
    sylancl
    wph
    @36
    c1
    wph
    @36
    @40
    nn0cnd
    wph
    c1
    @31
    recnd
    addcomd
    eqtr2d
    breqtrd
    ltletrd
    @11
    elnnz
    sylanbrc
    peano2nnd
    syl5eqel
    wph
    @1
    vr
    @2
    wph
    @0
    @2
    wcel
    #
    wa
    #
    vx
    cA
    cB
    cC
    cD
    @0
    cE
    cF
    cG
    cI
    cX
    cY
    vx
    cI
    cF
    cG
    cneg
    #
    cmul
    co
    #
    citg
    #
    cabs
    cfv
    #
    @45
    wph
    @0
    cr
    wcel
    #
    vx
    cI
    @48
    cmpt
    cibl
    wcel
    @0
    cM
    cpnf
    elioore
    #
    fourierdlem47.iblmul
    sylan2
    #
    wph
    @22
    cF
    cc
    wcel
    @45
    fourierdlem47.f
    adantlr
    #
    @46
    @22
    wa
    #
    wph
    @22
    @0
    cc
    wcel
    #
    cG
    cc
    wcel
    #
    wph
    @45
    @22
    simpll
    #
    @46
    @22
    simpr
    #
    @55
    @0
    @45
    @51
    wph
    @22
    @52
    ad2antlr
    #
    recnd
    fourierdlem47.g
    syl21anc
    #
    wph
    cA
    cc
    wcel
    @45
    fourierdlem47.a
    adantr
    fourierdlem47.x
    wph
    cC
    cc
    wcel
    @45
    fourierdlem47.c
    adantr
    fourierdlem47.y
    @50
    eqid
    wph
    cE
    crp
    wcel
    @45
    fourierdlem47.e
    adantr
    #
    @45
    @51
    wph
    @52
    adantl
    #
    @46
    @7
    @50
    caddc
    co
    #
    cE
    cdiv
    co
    #
    c1
    caddc
    co
    #
    @0
    @46
    @65
    c1
    @46
    @64
    cE
    @46
    @64
    @13
    @16
    caddc
    co
    #
    @50
    caddc
    co
    cr
    @67
    @7
    @50
    caddc
    @13
    cX
    @16
    cY
    caddc
    cX
    @13
    fourierdlem47.x
    eqcomi
    cY
    @16
    fourierdlem47.y
    eqcomi
    oveq12i
    oveq1i
    @46
    @67
    @50
    @46
    @13
    @16
    wph
    @13
    cr
    wcel
    @45
    @14
    adantr
    #
    wph
    @16
    cr
    wcel
    @45
    @17
    adantr
    #
    readdcld
    @46
    @49
    @46
    vx
    cI
    @48
    cc
    @55
    cF
    @47
    @54
    @55
    cG
    @61
    negcld
    #
    mulcld
    #
    @53
    itgcl
    abscld
    #
    readdcld
    syl5eqelr
    #
    wph
    cE
    cr
    wcel
    @45
    @28
    adantr
    #
    wph
    cE
    cc0
    wne
    @45
    @29
    adantr
    #
    redivcld
    #
    @46
    1red
    #
    readdcld
    #
    @63
    @46
    @66
    cM
    @0
    @78
    @46
    cM
    @12
    cr
    fourierdlem47.m
    @46
    @11
    c1
    @46
    @33
    @34
    @46
    @9
    c1
    @46
    @8
    cE
    @46
    @7
    cZ
    @46
    cX
    cY
    @46
    cX
    @13
    cr
    fourierdlem47.x
    @68
    syl5eqel
    @46
    cY
    @16
    cr
    fourierdlem47.y
    @69
    syl5eqel
    readdcld
    #
    wph
    cZ
    cr
    wcel
    @45
    @26
    adantr
    #
    readdcld
    #
    @74
    @75
    redivcld
    #
    @77
    readdcld
    @35
    syl
    #
    @77
    readdcld
    syl5eqel
    #
    @63
    @46
    @66
    @12
    cM
    clt
    @46
    @65
    @11
    c1
    @76
    @83
    @77
    @46
    @65
    @9
    @11
    @76
    @82
    @83
    @46
    @64
    @8
    cE
    @73
    @81
    @62
    @46
    @50
    cZ
    @7
    @72
    @80
    @79
    @46
    @50
    vx
    cI
    @48
    cabs
    cfv
    #
    citg
    #
    cZ
    @72
    @46
    vx
    cI
    @85
    @55
    @48
    @71
    abscld
    #
    @46
    vx
    cI
    @48
    cc
    @71
    @53
    iblabs
    #
    itgrecl
    @80
    @46
    vx
    cI
    @48
    cc
    @71
    @53
    itgabs
    @46
    @86
    @21
    cZ
    cle
    @46
    vx
    cI
    @85
    @20
    @88
    wph
    vx
    cI
    @20
    cmpt
    cibl
    wcel
    @45
    @25
    adantr
    @87
    @55
    cF
    @54
    abscld
    #
    @55
    @85
    @20
    @47
    cabs
    cfv
    #
    cmul
    co
    #
    @20
    cle
    @55
    cF
    @47
    @54
    @70
    absmuld
    @55
    @91
    @20
    c1
    cmul
    co
    @20
    cle
    @55
    @90
    c1
    @20
    @55
    @47
    @70
    abscld
    @55
    1red
    @89
    @55
    cF
    @54
    absge0d
    @55
    wph
    @22
    @51
    @90
    c1
    cle
    wbr
    @58
    @59
    @60
    @23
    @51
    wa
    #
    @90
    cG
    cabs
    cfv
    c1
    cle
    @92
    cG
    @51
    @23
    @56
    @57
    @0
    recn
    fourierdlem47.g
    sylan2
    absnegd
    fourierdlem47.absg
    eqbrtrd
    syl21anc
    lemul2ad
    @55
    @20
    @55
    @20
    @89
    recnd
    mulid1d
    breqtrd
    eqbrtrd
    itgle
    fourierdlem47.z
    syl6breqr
    letrd
    leadd2dd
    lediv1dd
    @46
    @9
    @41
    @11
    clt
    @46
    @39
    @9
    @41
    clt
    wbr
    @82
    @9
    flltp1
    syl
    @46
    @39
    @42
    @43
    @82
    1z
    @44
    sylancl
    breqtrrd
    lelttrd
    ltadd1dd
    fourierdlem47.m
    syl6breqr
    @46
    cM
    cxr
    wcel
    cpnf
    cxr
    wcel
    #
    @45
    cM
    @0
    clt
    wbr
    @46
    cM
    @84
    rexrd
    @93
    @46
    pnfxr
    a1i
    wph
    @45
    simpr
    cM
    cpnf
    @0
    ioogtlb
    syl3anc
    lttrd
    ltled
    wph
    @45
    @56
    cB
    cc
    wcel
    @46
    @0
    @63
    recnd
    #
    fourierdlem47.b
    syldan
    @45
    wph
    @51
    cB
    cabs
    cfv
    c1
    cle
    wbr
    @52
    fourierdlem47.absb
    sylan2
    wph
    @45
    @56
    cD
    cc
    wcel
    @94
    fourierdlem47.d
    syldan
    @45
    wph
    @51
    cD
    cabs
    cfv
    c1
    cle
    wbr
    @52
    fourierdlem47.absd
    sylan2
    fourierdlem30
    ralrimiva
    @6
    @3
    vm
    cM
    cn
    @4
    cM
    wceq
    @1
    vr
    @5
    @2
    @4
    cM
    cpnf
    cioo
    oveq1
    raleqdv
    rspcev
    syl2anc
end
