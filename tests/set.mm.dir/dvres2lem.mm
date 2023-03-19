include "cv.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "wbr.mm"
include "cin.mm"
include "crest.mm"
include "cnt.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cuni.mm"
include "cun.mm"
include "ctop.mm"
include "wss.mm"
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
include "wceq.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "toponuni.mm"
include "syl.mm"
include "sseqtrd.mm"
include "difssd.mm"
include "unssd.mm"
include "inundif.mm"
include "ssdif.mm"
include "unss2.mm"
include "3syl.mm"
include "syl5eqssr.mm"
include "eqid.mm"
include "ntrss.mm"
include "syl3anc.mm"
include "wa.mm"
include "eldv.mm"
include "mpbid.mm"
include "simpld.mm"
include "sseldd.mm"
include "elind.mm"
include "inss2.mm"
include "a1i.mm"
include "restntr.mm"
include "oveq1i.mm"
include "restabs.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "limcresi.mm"
include "simprd.mm"
include "sseldi.mm"
include "difss.mm"
include "sstri.mm"
include "sseli.mm"
include "fvres.mm"
include "oveqan12rd.mm"
include "oveq1d.mm"
include "sylan2.mm"
include "mpteq2dva.mm"
include "reseq1i.mm"
include "resmpt.mm"
include "mp2b.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "sstrd.mm"
include "wf.mm"
include "fresin.mm"
include "mpbir2and.mm"

theorem dvres2lem
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
  assume dvres2lem.d: |- ( ph -> x ( S _D F ) y )
  assume dvres2lem.x: |- ( ph -> x e. B )

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
  assert |- ( ph -> x ( B _D ( F |` B ) ) y )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cB
    cF
    cB
    cres
    #
    cdv
    co
    wbr
    @0
    cA
    cB
    cin
    #
    cK
    cB
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    wcel
    @1
    vz
    @3
    @0
    csn
    #
    cdif
    #
    vz
    cv
    #
    @2
    cfv
    #
    @0
    @2
    cfv
    #
    cmin
    co
    #
    @9
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
    wph
    @0
    @3
    cT
    cuni
    #
    cB
    cdif
    #
    cun
    #
    cT
    cnt
    cfv
    #
    cfv
    #
    cB
    cin
    #
    @6
    wph
    @21
    cB
    @0
    wph
    cA
    @20
    cfv
    #
    @21
    @0
    wph
    cT
    ctop
    wcel
    #
    @19
    @17
    wss
    cA
    @19
    wss
    @23
    @21
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
    @25
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
    @27
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
    @3
    @18
    @17
    wph
    @3
    cS
    @17
    wph
    @3
    cA
    cS
    cA
    cB
    inss1
    #
    dvres.a
    syl5ss
    wph
    cT
    cS
    ctopon
    cfv
    #
    wcel
    cS
    @17
    wceq
    wph
    cT
    @25
    @33
    dvres.t
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    @29
    @25
    @33
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
    wph
    @17
    cB
    difssd
    unssd
    wph
    cA
    @3
    cA
    cB
    cdif
    #
    cun
    #
    @19
    cA
    cB
    inundif
    wph
    cA
    @17
    wss
    @35
    @18
    wss
    @36
    @19
    wss
    wph
    cA
    cS
    @17
    dvres.a
    @34
    sseqtrd
    cA
    @17
    cB
    ssdif
    @35
    @18
    @3
    unss2
    3syl
    syl5eqssr
    @19
    cA
    cT
    @17
    @17
    eqid
    #
    ntrss
    syl3anc
    wph
    @0
    @23
    wcel
    #
    @1
    cG
    @0
    climc
    co
    #
    wcel
    #
    wph
    @0
    @1
    cS
    cF
    cdv
    co
    wbr
    @38
    @40
    wa
    dvres2lem.d
    wph
    vz
    cA
    @0
    @1
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
    mpbid
    #
    simpld
    sseldd
    dvres2lem.x
    elind
    wph
    @3
    cT
    cB
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @22
    @6
    wph
    @24
    cB
    @17
    wss
    @3
    cB
    wss
    #
    @44
    @22
    wceq
    @31
    wph
    cB
    cS
    @17
    dvres.b
    @34
    sseqtrd
    @45
    wph
    cA
    cB
    inss2
    #
    a1i
    #
    @3
    cT
    @42
    @17
    cB
    @37
    @42
    eqid
    restntr
    syl3anc
    wph
    @3
    @43
    @5
    wph
    @42
    @4
    cnt
    wph
    @42
    @25
    cB
    crest
    co
    #
    @4
    cT
    @25
    cB
    crest
    dvres.t
    oveq1i
    wph
    @26
    cB
    cS
    wss
    @27
    @48
    @4
    wceq
    @26
    wph
    @28
    a1i
    dvres.b
    @30
    cB
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
    eleqtrd
    wph
    @1
    cG
    @8
    cres
    #
    @0
    climc
    co
    #
    @16
    wph
    @39
    @50
    @1
    @0
    @8
    cG
    limcresi
    wph
    @38
    @40
    @41
    simprd
    sseldi
    wph
    @15
    @49
    @0
    climc
    wph
    @15
    vz
    @8
    @9
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
    @49
    wph
    vz
    @8
    @14
    @54
    @9
    @8
    wcel
    wph
    @9
    cB
    wcel
    #
    @14
    @54
    wceq
    @8
    cB
    @9
    @8
    @3
    cB
    @3
    @7
    difss
    @46
    sstri
    sseli
    wph
    @56
    wa
    @12
    @53
    @13
    cdiv
    @56
    wph
    @10
    @51
    @11
    @52
    cmin
    @9
    cB
    cF
    fvres
    wph
    @0
    cB
    wcel
    @11
    @52
    wceq
    dvres2lem.x
    @0
    cB
    cF
    fvres
    syl
    oveqan12rd
    oveq1d
    sylan2
    mpteq2dva
    @49
    vz
    cA
    @7
    cdif
    #
    @54
    cmpt
    #
    @8
    cres
    #
    @55
    cG
    @58
    @8
    dvres.g
    reseq1i
    @3
    cA
    wss
    @8
    @57
    wss
    @59
    @55
    wceq
    @32
    @3
    cA
    @7
    ssdif
    vz
    @57
    @8
    @54
    resmpt
    mp2b
    eqtri
    syl6eqr
    oveq1d
    eleqtrrd
    wph
    vz
    @3
    @0
    @1
    cB
    @4
    @2
    @15
    cK
    @4
    eqid
    dvres.k
    @15
    eqid
    wph
    cB
    cS
    cc
    dvres.b
    dvres.s
    sstrd
    wph
    cA
    cc
    cF
    wf
    @3
    cc
    @2
    wf
    dvres.f
    cA
    cc
    cF
    cB
    fresin
    syl
    @47
    eldv
    mpbir2and
end
