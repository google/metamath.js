include "cibl.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "wceq.mm"
include "cr.mm"
include "cc.mm"
include "ccncf.mm"
include "cioo.mm"
include "cres.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "wn.mm"
include "ifeq2d.mm"
include "adantll.mm"
include "iffalse.mm"
include "ad2antlr.mm"
include "cxr.mm"
include "adantr.mm"
include "rexrd.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "iccgelb.mm"
include "wne.mm"
include "neqne.mm"
include "leneltd.mm"
include "iccleub.mm"
include "eqcom.mm"
include "notbii.mm"
include "biimpi.mm"
include "neqned.mm"
include "adantlr.mm"
include "eliood.mm"
include "fvres.mm"
include "syl.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "nfv.mm"
include "eqid.mm"
include "cncfiooicc.mm"
include "eqeltrd.mm"
include "cniccibl.mm"
include "climc.mm"
include "limccl.mm"
include "sseldi.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "wf.mm"
include "cncff.mm"
include "ffvelrnd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "itgioo.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "eliooord.mm"
include "simpld.mm"
include "gtned.mm"
include "neneqd.mm"
include "simprd.mm"
include "ltned.mm"
include "itgeq2dv.mm"
include "cdm.mm"
include "sselda.mm"
include "jca.mm"

theorem itgioocnicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let vk: setvar k
  assume itgioocnicc.a: |- ( ph -> A e. RR )
  assume itgioocnicc.b: |- ( ph -> B e. RR )
  assume itgioocnicc.f: |- ( ph -> F : dom F --> CC )
  assume itgioocnicc.fcn: |- ( ph -> ( F |` ( A (,) B ) ) e. ( ( A (,) B ) -cn-> CC ) )
  assume itgioocnicc.fdom: |- ( ph -> ( A [,] B ) C_ dom F )
  assume itgioocnicc.r: |- ( ph -> R e. ( ( F |` ( A (,) B ) ) limCC A ) )
  assume itgioocnicc.l: |- ( ph -> L e. ( ( F |` ( A (,) B ) ) limCC B ) )
  assume itgioocnicc.g: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( F ` x ) ) ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint L x
  disjoint R x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( G e. L^1 /\ S. ( A [,] B ) ( G ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x ) )

  proof
    wph
    cG
    cibl
    wcel
    #
    vx
    cA
    cB
    cicc
    co
    #
    vx
    cv
    #
    cG
    cfv
    #
    citg
    #
    vx
    @1
    @2
    cF
    cfv
    #
    citg
    #
    wceq
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cG
    @1
    cc
    ccncf
    co
    #
    wcel
    @0
    itgioocnicc.a
    itgioocnicc.b
    wph
    cG
    vx
    @1
    @2
    cA
    wceq
    #
    cR
    @2
    cB
    wceq
    #
    cL
    @2
    cF
    cA
    cB
    cioo
    co
    #
    cres
    #
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    @9
    wph
    cG
    vx
    @1
    @10
    cR
    @11
    cL
    @5
    cif
    #
    cif
    #
    cmpt
    @17
    itgioocnicc.g
    wph
    vx
    @1
    @19
    @16
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @10
    @19
    @16
    wceq
    #
    @10
    @22
    @21
    @10
    @19
    cR
    @16
    @10
    cR
    @18
    iftrue
    #
    @10
    cR
    @15
    iftrue
    eqtr4d
    adantl
    @21
    @10
    wn
    #
    wa
    #
    @11
    @22
    @24
    @11
    @22
    @21
    @24
    @11
    wa
    @10
    @18
    @15
    cR
    @11
    @18
    @15
    wceq
    @24
    @11
    @18
    cL
    @15
    @11
    cL
    @5
    iftrue
    #
    @11
    cL
    @14
    iftrue
    eqtr4d
    adantl
    ifeq2d
    adantll
    @25
    @11
    wn
    #
    wa
    #
    @19
    @18
    @5
    @16
    @24
    @19
    @18
    wceq
    #
    @21
    @27
    @10
    cR
    @18
    iffalse
    #
    ad2antlr
    @27
    @18
    @5
    wceq
    #
    @25
    @11
    cL
    @5
    iffalse
    #
    adantl
    @28
    @16
    @15
    @14
    @5
    @24
    @16
    @15
    wceq
    @21
    @27
    @10
    cR
    @15
    iffalse
    ad2antlr
    @27
    @15
    @14
    wceq
    @25
    @11
    cL
    @14
    iffalse
    adantl
    @28
    @2
    @12
    wcel
    #
    @14
    @5
    wceq
    @28
    cA
    cB
    @2
    @21
    cA
    cxr
    wcel
    #
    @24
    @27
    @21
    cA
    wph
    @7
    @20
    itgioocnicc.a
    adantr
    #
    rexrd
    #
    ad2antrr
    wph
    cB
    cxr
    wcel
    #
    @20
    @24
    @27
    wph
    cB
    itgioocnicc.b
    rexrd
    #
    ad3antrrr
    @21
    @2
    cr
    wcel
    #
    @24
    @27
    @21
    @7
    @8
    @20
    @39
    @35
    wph
    @8
    @20
    itgioocnicc.b
    adantr
    wph
    @20
    simpr
    #
    cA
    cB
    @2
    eliccre
    syl3anc
    #
    ad2antrr
    @25
    cA
    @2
    clt
    wbr
    #
    @27
    @25
    cA
    @2
    wph
    @7
    @20
    @24
    itgioocnicc.a
    ad2antrr
    @21
    @39
    @24
    @41
    adantr
    @21
    cA
    @2
    cle
    wbr
    #
    @24
    @21
    @34
    @37
    @20
    @43
    @36
    wph
    @37
    @20
    @38
    adantr
    #
    @40
    cA
    cB
    @2
    iccgelb
    syl3anc
    adantr
    @24
    @2
    cA
    wne
    @21
    @2
    cA
    neqne
    adantl
    leneltd
    adantr
    @21
    @27
    @2
    cB
    clt
    wbr
    #
    @24
    @21
    @27
    wa
    @2
    cB
    @21
    @39
    @27
    @41
    adantr
    wph
    @8
    @20
    @27
    itgioocnicc.b
    ad2antrr
    @21
    @2
    cB
    cle
    wbr
    #
    @27
    @21
    @34
    @37
    @20
    @46
    @36
    @44
    @40
    cA
    cB
    @2
    iccleub
    syl3anc
    adantr
    @27
    cB
    @2
    wne
    @21
    @27
    cB
    @2
    @27
    cB
    @2
    wceq
    #
    wn
    @11
    @47
    @2
    cB
    eqcom
    notbii
    biimpi
    neqned
    adantl
    leneltd
    adantlr
    eliood
    #
    @2
    @12
    cF
    fvres
    syl
    #
    3eqtrrd
    3eqtrd
    pm2.61dan
    pm2.61dan
    mpteq2dva
    syl5eq
    wph
    vx
    cA
    cB
    cR
    @13
    @17
    cL
    wph
    vx
    nfv
    @17
    eqid
    itgioocnicc.a
    itgioocnicc.b
    itgioocnicc.fcn
    itgioocnicc.l
    itgioocnicc.r
    cncfiooicc
    eqeltrd
    cA
    cB
    cG
    cniccibl
    syl3anc
    wph
    @4
    vx
    @12
    @3
    citg
    #
    vx
    @12
    @5
    citg
    @6
    wph
    @50
    @4
    wph
    vx
    cA
    cB
    @3
    itgioocnicc.a
    itgioocnicc.b
    @21
    @3
    @19
    cc
    @21
    @20
    @19
    cc
    wcel
    #
    @3
    @19
    wceq
    #
    @40
    @21
    @10
    @51
    @21
    @10
    wa
    @19
    cR
    cc
    @10
    @19
    cR
    wceq
    @21
    @23
    adantl
    wph
    cR
    cc
    wcel
    @20
    @10
    wph
    @13
    cA
    climc
    co
    cc
    cR
    cA
    @13
    limccl
    itgioocnicc.r
    sseldi
    ad2antrr
    eqeltrd
    @25
    @11
    @51
    @25
    @11
    wa
    @19
    cL
    cc
    @24
    @11
    @19
    cL
    wceq
    @21
    @24
    @11
    @19
    @18
    cL
    @30
    @26
    sylan9eq
    adantll
    wph
    cL
    cc
    wcel
    @20
    @24
    @11
    wph
    @13
    cB
    climc
    co
    cc
    cL
    cB
    @13
    limccl
    itgioocnicc.l
    sseldi
    ad3antrrr
    eqeltrd
    @28
    @19
    @5
    cc
    @24
    @27
    @19
    @5
    wceq
    @21
    @24
    @27
    @19
    @18
    @5
    @30
    @32
    sylan9eq
    adantll
    @28
    @5
    @14
    cc
    @28
    @14
    @5
    @49
    eqcomd
    @28
    @12
    cc
    @2
    @13
    wph
    @12
    cc
    @13
    wf
    #
    @20
    @24
    @27
    wph
    @13
    @12
    cc
    ccncf
    co
    wcel
    @53
    itgioocnicc.fcn
    @12
    cc
    @13
    cncff
    syl
    ad3antrrr
    @48
    ffvelrnd
    eqeltrd
    eqeltrd
    pm2.61dan
    pm2.61dan
    #
    vx
    @1
    @19
    cc
    cG
    itgioocnicc.g
    fvmpt2
    syl2anc
    #
    @54
    eqeltrd
    itgioo
    eqcomd
    wph
    vx
    @12
    @3
    @5
    wph
    @33
    wa
    #
    @3
    @19
    @18
    @5
    @33
    wph
    @20
    @52
    @12
    @1
    @2
    cA
    cB
    ioossicc
    sseli
    #
    @55
    sylan2
    @56
    @24
    @29
    @56
    @2
    cA
    @56
    cA
    @2
    wph
    @7
    @33
    itgioocnicc.a
    adantr
    @33
    @42
    wph
    @33
    @42
    @45
    @2
    cA
    cB
    eliooord
    #
    simpld
    adantl
    gtned
    neneqd
    @30
    syl
    @56
    @27
    @31
    @56
    @2
    cB
    @56
    @2
    cB
    @33
    wph
    @20
    @39
    @57
    @41
    sylan2
    @33
    @45
    wph
    @33
    @42
    @45
    @58
    simprd
    adantl
    ltned
    neneqd
    @32
    syl
    3eqtrd
    itgeq2dv
    wph
    vx
    cA
    cB
    @5
    itgioocnicc.a
    itgioocnicc.b
    @21
    cF
    cdm
    #
    cc
    @2
    cF
    wph
    @59
    cc
    cF
    wf
    @20
    itgioocnicc.f
    adantr
    wph
    @1
    @59
    @2
    itgioocnicc.fdom
    sselda
    ffvelrnd
    itgioo
    3eqtrd
    jca
end
