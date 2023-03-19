include "cioo.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cibl.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "feqmptd.mm"
include "wa.mm"
include "cr.mm"
include "adantr.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "adantl.mm"
include "gtned.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "elioore.mm"
include "simprd.mm"
include "ltned.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "cicc.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "iftrue.mm"
include "climc.mm"
include "limccl.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "iffalse.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "adantllr.mm"
include "simplll.mm"
include "cxr.mm"
include "w3a.mm"
include "rexrd.mm"
include "eliccxr.mm"
include "ad3antlr.mm"
include "3jca.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "cle.mm"
include "wb.mm"
include "jca.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp2d.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "leneltd.mm"
include "nesym.mm"
include "simp3d.mm"
include "leltne.mm"
include "mpbird.mm"
include "elioo3g.mm"
include "sylanbrc.mm"
include "ffvelrnda.mm"
include "pm2.61dan.mm"
include "nfv.mm"
include "eqid.mm"
include "cncfiooicc.mm"
include "cniccibl.mm"
include "iblss.mm"

theorem iblcncfioo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cL: class L
  let vx: setvar x
  let vk: setvar k
  assume iblcncfioo.a: |- ( ph -> A e. RR )
  assume iblcncfioo.b: |- ( ph -> B e. RR )
  assume iblcncfioo.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume iblcncfioo.l: |- ( ph -> L e. ( F limCC B ) )
  assume iblcncfioo.r: |- ( ph -> R e. ( F limCC A ) )


  assert |- ( ph -> F e. L^1 )

  proof
    wph
    cF
    vx
    cA
    cB
    cioo
    co
    #
    vx
    cv
    #
    cA
    wceq
    #
    cR
    @1
    cB
    wceq
    #
    cL
    @1
    cF
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    cibl
    wph
    cF
    vx
    @0
    @4
    cmpt
    @7
    wph
    vx
    @0
    cc
    cF
    wph
    cF
    @0
    cc
    ccncf
    co
    wcel
    @0
    cc
    cF
    wf
    iblcncfioo.f
    @0
    cc
    cF
    cncff
    syl
    #
    feqmptd
    wph
    vx
    @0
    @4
    @6
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @6
    @4
    @10
    @6
    @5
    @4
    @10
    @2
    cR
    @5
    @10
    @1
    cA
    @10
    cA
    @1
    wph
    cA
    cr
    wcel
    #
    @9
    iblcncfioo.a
    adantr
    @9
    cA
    @1
    clt
    wbr
    #
    wph
    @9
    @12
    @1
    cB
    clt
    wbr
    #
    @1
    cA
    cB
    eliooord
    #
    simpld
    adantl
    gtned
    neneqd
    iffalsed
    @10
    @3
    cL
    @4
    @10
    @1
    cB
    @10
    @1
    cB
    @9
    @1
    cr
    wcel
    #
    wph
    @1
    cA
    cB
    elioore
    adantl
    @9
    @13
    wph
    @9
    @12
    @13
    @14
    simprd
    adantl
    ltned
    neneqd
    iffalsed
    eqtrd
    #
    eqcomd
    mpteq2dva
    eqtrd
    wph
    vx
    @0
    cA
    cB
    cicc
    co
    #
    @6
    cc
    @0
    @17
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    @0
    cvol
    cdm
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @1
    @17
    wcel
    #
    wa
    #
    @2
    @6
    cc
    wcel
    #
    wph
    @2
    @20
    @18
    wph
    @2
    wa
    @6
    cR
    cc
    @2
    @6
    cR
    wceq
    wph
    @2
    cR
    @5
    iftrue
    adantl
    wph
    cR
    cc
    wcel
    @2
    wph
    cF
    cA
    climc
    co
    cc
    cR
    cA
    cF
    limccl
    iblcncfioo.r
    sseldi
    adantr
    eqeltrd
    adantlr
    @19
    @2
    wn
    #
    wa
    #
    @3
    @20
    wph
    @21
    @3
    @20
    @18
    wph
    @21
    wa
    #
    @3
    wa
    #
    @6
    cL
    cc
    @24
    @6
    @5
    cL
    @21
    @6
    @5
    wceq
    wph
    @3
    @2
    cR
    @5
    iffalse
    ad2antlr
    @3
    @5
    cL
    wceq
    @23
    @3
    cL
    @4
    iftrue
    adantl
    eqtrd
    wph
    cL
    cc
    wcel
    @21
    @3
    wph
    cF
    cB
    climc
    co
    cc
    cL
    cB
    cF
    limccl
    iblcncfioo.l
    sseldi
    ad2antrr
    eqeltrd
    adantllr
    @22
    @3
    wn
    #
    wa
    #
    @10
    @20
    @26
    wph
    @9
    wph
    @18
    @21
    @25
    simplll
    #
    @26
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    w3a
    @12
    @13
    wa
    @9
    @26
    @28
    @29
    @30
    @26
    wph
    @28
    @27
    wph
    cA
    iblcncfioo.a
    rexrd
    syl
    @26
    wph
    @29
    @27
    wph
    cB
    iblcncfioo.b
    rexrd
    syl
    @18
    @30
    wph
    @21
    @25
    @1
    cA
    cB
    eliccxr
    ad3antlr
    3jca
    @26
    @12
    @13
    @22
    @12
    @25
    @22
    cA
    @1
    wph
    @11
    @18
    @21
    iblcncfioo.a
    ad2antrr
    @19
    @15
    @21
    @19
    @11
    cB
    cr
    wcel
    #
    @18
    @15
    wph
    @11
    @18
    iblcncfioo.a
    adantr
    wph
    @31
    @18
    iblcncfioo.b
    adantr
    #
    wph
    @18
    simpr
    #
    cA
    cB
    @1
    eliccre
    syl3anc
    #
    adantr
    @19
    cA
    @1
    cle
    wbr
    #
    @21
    @19
    @15
    @35
    @1
    cB
    cle
    wbr
    #
    @19
    @18
    @15
    @35
    @36
    w3a
    #
    @33
    @19
    @11
    @31
    wa
    #
    @18
    @37
    wb
    wph
    @38
    @18
    wph
    @11
    @31
    iblcncfioo.a
    iblcncfioo.b
    jca
    adantr
    cA
    cB
    @1
    elicc2
    syl
    mpbid
    #
    simp2d
    adantr
    @21
    @1
    cA
    wne
    #
    @19
    @40
    @21
    @1
    cA
    df-ne
    biimpri
    adantl
    leneltd
    adantr
    @19
    @25
    @13
    @21
    @19
    @25
    wa
    #
    @13
    cB
    @1
    wne
    #
    @25
    @42
    @19
    @42
    @25
    cB
    @1
    nesym
    biimpri
    adantl
    @41
    @15
    @31
    @36
    w3a
    #
    @13
    @42
    wb
    @19
    @43
    @25
    @19
    @15
    @31
    @36
    @34
    @32
    @19
    @15
    @35
    @36
    @39
    simp3d
    3jca
    adantr
    @1
    cB
    leltne
    syl
    mpbird
    adantlr
    jca
    cA
    cB
    @1
    elioo3g
    sylanbrc
    jca
    @10
    @6
    @4
    cc
    @16
    wph
    @0
    cc
    @1
    cF
    @8
    ffvelrnda
    eqeltrd
    syl
    pm2.61dan
    pm2.61dan
    wph
    @11
    @31
    vx
    @17
    @6
    cmpt
    #
    @17
    cc
    ccncf
    co
    wcel
    @44
    cibl
    wcel
    iblcncfioo.a
    iblcncfioo.b
    wph
    vx
    cA
    cB
    cR
    cF
    @44
    cL
    wph
    vx
    nfv
    @44
    eqid
    iblcncfioo.a
    iblcncfioo.b
    iblcncfioo.f
    iblcncfioo.l
    iblcncfioo.r
    cncfiooicc
    cA
    cB
    @44
    cniccibl
    syl3anc
    iblss
    eqeltrd
end
