include "cv.mm"
include "cin.mm"
include "cnt.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "wa.mm"
include "cdv.mm"
include "wbr.mm"
include "wceq.mm"
include "difss.mm"
include "inss2.mm"
include "sstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "fvres.mm"
include "syl.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "crest.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "cc.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "resttop.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "inss1.mm"
include "syl5ss.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "syl6ss.mm"
include "sselda.mm"
include "adantr.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "reseq1i.mm"
include "ssdif.mm"
include "resmpt.mm"
include "mp2b.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "cun.mm"
include "wf.mm"
include "sstrd.mm"
include "dvlem.mm"
include "fmptd.mm"
include "mp1i.mm"
include "difssd.mm"
include "unssd.mm"
include "ssun1.mm"
include "a1i.mm"
include "ntrss.mm"
include "syl3anc.mm"
include "ssind.mm"
include "restntr.mm"
include "oveq1i.mm"
include "restabs.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "undif1.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "oveq2d.mm"
include "fveq12d.mm"
include "eleqtrrd.mm"
include "limcres.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "pm5.32da.mm"
include "ntrin.mm"
include "elin.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "an32.mm"
include "fresin.mm"
include "eldv.mm"
include "3bitr4d.mm"

theorem dvreslem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cK: class K
  assume dvres.k: |- K = ( TopOpen ` CCfld )
  assume dvres.t: |- T = ( K |`t S )
  assume dvres.g: |- G = ( z e. ( A \ { x } ) |-> ( ( ( F ` z ) - ( F ` x ) ) / ( z - x ) ) )
  assume dvres.s: |- ( ph -> S C_ CC )
  assume dvres.f: |- ( ph -> F : A --> CC )
  assume dvres.a: |- ( ph -> A C_ S )
  assume dvres.b: |- ( ph -> B C_ S )
  assume dvres.y: |- ( ph -> y e. CC )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint K z
  disjoint ph z
  assert |- ( ph -> ( x ( S _D ( F |` B ) ) y <-> ( x ( S _D F ) y /\ x e. ( ( int ` T ) ` B ) ) ) )

  proof
    wph
    vx
    cv
    #
    cA
    cB
    cin
    #
    cT
    cnt
    cfv
    #
    cfv
    #
    wcel
    #
    vy
    cv
    #
    vz
    @1
    @0
    csn
    #
    cdif
    #
    vz
    cv
    #
    cF
    cB
    cres
    #
    cfv
    #
    @0
    @9
    cfv
    #
    cmin
    co
    #
    @8
    @0
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @0
    climc
    co
    #
    wcel
    #
    wa
    #
    @0
    cA
    @2
    cfv
    #
    wcel
    #
    @5
    cG
    @0
    climc
    co
    #
    wcel
    #
    wa
    #
    @0
    cB
    @2
    cfv
    #
    wcel
    #
    wa
    #
    @0
    @5
    cS
    @9
    cdv
    co
    wbr
    @0
    @5
    cS
    cF
    cdv
    co
    wbr
    #
    @25
    wa
    wph
    @18
    @20
    @25
    wa
    #
    @22
    wa
    #
    @26
    wph
    @18
    @4
    @22
    wa
    @29
    wph
    @4
    @17
    @22
    wph
    @4
    wa
    #
    @16
    @21
    @5
    @30
    @16
    cG
    @7
    cres
    #
    @0
    climc
    co
    @21
    @30
    @15
    @31
    @0
    climc
    @30
    @15
    vz
    @7
    @8
    cF
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    #
    @13
    cdiv
    co
    #
    cmpt
    #
    @31
    @30
    vz
    @7
    @14
    @35
    @30
    @8
    @7
    wcel
    #
    wa
    #
    @12
    @34
    @13
    cdiv
    @38
    @10
    @32
    @11
    @33
    cmin
    @38
    @8
    cB
    wcel
    @10
    @32
    wceq
    @38
    @7
    cB
    @8
    @7
    @1
    cB
    @1
    @6
    difss
    cA
    cB
    inss2
    #
    sstri
    @30
    @37
    simpr
    sseldi
    @8
    cB
    cF
    fvres
    syl
    @30
    @11
    @33
    wceq
    #
    @37
    @30
    @0
    cB
    wcel
    @40
    wph
    @3
    cB
    @0
    wph
    @3
    @1
    cB
    wph
    cT
    ctop
    wcel
    #
    @1
    cT
    cuni
    #
    wss
    @3
    @1
    wss
    wph
    cT
    cK
    cS
    crest
    co
    #
    ctop
    dvres.t
    wph
    cK
    ctop
    wcel
    #
    cS
    cvv
    wcel
    #
    @43
    ctop
    wcel
    cK
    dvres.k
    cnfldtop
    #
    wph
    cS
    cc
    wss
    #
    cc
    cvv
    wcel
    @45
    dvres.s
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    #
    cS
    cK
    cvv
    resttop
    sylancr
    syl5eqel
    #
    wph
    @1
    cS
    @42
    wph
    @1
    cA
    cS
    cA
    cB
    inss1
    #
    dvres.a
    syl5ss
    #
    wph
    cT
    cS
    ctopon
    cfv
    #
    wcel
    cS
    @42
    wceq
    wph
    cT
    @43
    @52
    dvres.t
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    @47
    @43
    @52
    wcel
    cK
    dvres.k
    cnfldtopon
    dvres.s
    cS
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    cS
    cT
    toponuni
    syl
    #
    sseqtrd
    #
    @1
    cT
    @42
    @42
    eqid
    #
    ntrss2
    syl2anc
    #
    @39
    syl6ss
    sselda
    @0
    cB
    cF
    fvres
    syl
    adantr
    oveq12d
    oveq1d
    mpteq2dva
    @31
    vz
    cA
    @6
    cdif
    #
    @35
    cmpt
    #
    @7
    cres
    #
    @36
    cG
    @58
    @7
    dvres.g
    reseq1i
    @1
    cA
    wss
    #
    @7
    @57
    wss
    #
    @59
    @36
    wceq
    @50
    @1
    cA
    @6
    ssdif
    #
    vz
    @57
    @7
    @35
    resmpt
    mp2b
    eqtri
    syl6eqr
    oveq1d
    @30
    @57
    @0
    @7
    cG
    cK
    @57
    @6
    cun
    #
    crest
    co
    #
    cK
    @30
    vz
    @57
    @35
    cc
    cG
    @30
    @8
    @0
    cA
    cF
    wph
    cA
    cc
    cF
    wf
    #
    @4
    dvres.f
    adantr
    wph
    cA
    cc
    wss
    @4
    wph
    cA
    cS
    cc
    dvres.a
    dvres.s
    sstrd
    adantr
    #
    wph
    @3
    cA
    @0
    wph
    @3
    @1
    cA
    @56
    @50
    syl6ss
    #
    sselda
    dvlem
    dvres.g
    fmptd
    @60
    @61
    @30
    @50
    @62
    mp1i
    @30
    @57
    cA
    cc
    cA
    @6
    difss
    @66
    syl5ss
    dvres.k
    @64
    eqid
    @30
    @0
    @1
    cK
    cA
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @7
    @6
    cun
    #
    @64
    cnt
    cfv
    #
    cfv
    wph
    @3
    @70
    @0
    wph
    @3
    @1
    @42
    cA
    cdif
    #
    cun
    #
    @2
    cfv
    #
    cA
    cin
    #
    @70
    wph
    @3
    @75
    cA
    wph
    @41
    @74
    @42
    wss
    @1
    @74
    wss
    #
    @3
    @75
    wss
    @49
    wph
    @1
    @73
    @42
    @54
    wph
    @42
    cA
    difssd
    unssd
    @77
    wph
    @1
    @73
    ssun1
    a1i
    @74
    @1
    cT
    @42
    @55
    ntrss
    syl3anc
    @67
    ssind
    wph
    @1
    cT
    cA
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @76
    @70
    wph
    @41
    cA
    @42
    wss
    #
    @60
    @80
    @76
    wceq
    @49
    wph
    cA
    cS
    @42
    dvres.a
    @53
    sseqtrd
    #
    @60
    wph
    @50
    a1i
    @1
    cT
    @78
    @42
    cA
    @55
    @78
    eqid
    restntr
    syl3anc
    wph
    @1
    @79
    @69
    wph
    @78
    @68
    cnt
    wph
    @78
    @43
    cA
    crest
    co
    #
    @68
    cT
    @43
    cA
    crest
    dvres.t
    oveq1i
    wph
    @44
    cA
    cS
    wss
    @45
    @83
    @68
    wceq
    @44
    wph
    @46
    a1i
    dvres.a
    @48
    cA
    cS
    cK
    ctop
    cvv
    restabs
    syl3anc
    syl5eq
    fveq2d
    fveq1d
    eqtr3d
    sseqtrd
    sselda
    @30
    @71
    @1
    @72
    @69
    @30
    @64
    @68
    cnt
    @30
    @63
    cA
    cK
    crest
    @30
    @63
    cA
    @6
    cun
    #
    cA
    cA
    @6
    undif1
    @30
    @6
    cA
    wss
    @84
    cA
    wceq
    @30
    @6
    @1
    cA
    @30
    @0
    @1
    wph
    @3
    @1
    @0
    @56
    sselda
    snssd
    #
    @50
    syl6ss
    @6
    cA
    ssequn2
    sylib
    syl5eq
    oveq2d
    fveq2d
    @30
    @71
    @1
    @6
    cun
    #
    @1
    @1
    @6
    undif1
    @30
    @6
    @1
    wss
    @86
    @1
    wceq
    @85
    @6
    @1
    ssequn2
    sylib
    syl5eq
    fveq12d
    eleqtrrd
    limcres
    eqtrd
    eleq2d
    pm5.32da
    wph
    @4
    @28
    @22
    wph
    @4
    @0
    @19
    @24
    cin
    #
    wcel
    @28
    wph
    @3
    @87
    @0
    wph
    @41
    @81
    cB
    @42
    wss
    @3
    @87
    wceq
    @49
    @82
    wph
    cB
    cS
    @42
    dvres.b
    @53
    sseqtrd
    cA
    cB
    cT
    @42
    @55
    ntrin
    syl3anc
    eleq2d
    @0
    @19
    @24
    elin
    syl6bb
    anbi1d
    bitrd
    @20
    @25
    @22
    an32
    syl6bb
    wph
    vz
    @1
    @0
    @5
    cS
    cT
    @9
    @15
    cK
    dvres.t
    dvres.k
    @15
    eqid
    dvres.s
    wph
    @65
    @1
    cc
    @9
    wf
    dvres.f
    cA
    cc
    cF
    cB
    fresin
    syl
    @51
    eldv
    wph
    @27
    @23
    @25
    wph
    vz
    cA
    @0
    @5
    cS
    cT
    cF
    cG
    cK
    dvres.t
    dvres.k
    dvres.g
    dvres.s
    dvres.f
    dvres.a
    eldv
    anbi1d
    3bitr4d
end
