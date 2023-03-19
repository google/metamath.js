include "cicc.mm"
include "co.mm"
include "cr.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "cioo.mm"
include "cncff.mm"
include "syl.mm"
include "cc.mm"
include "wss.mm"
include "ioosscn.mm"
include "a1i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "rexrd.mm"
include "lptioo1cn.mm"
include "limcrecl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "adantll.mm"
include "lptioo2cn.mm"
include "ad2antrr.mm"
include "adantllr.mm"
include "ad3antrrr.mm"
include "cxr.mm"
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
include "necomd.mm"
include "eliood.mm"
include "ffvelrnd.mm"
include "pm2.61dan.mm"
include "fmptd.mm"
include "wb.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "cncfiooicc.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem cncfiooiccre
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let vk: setvar k
  assume cncfiooiccre.x: |- F/ x ph
  assume cncfiooiccre.g: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( F ` x ) ) ) )
  assume cncfiooiccre.a: |- ( ph -> A e. RR )
  assume cncfiooiccre.b: |- ( ph -> B e. RR )
  assume cncfiooiccre.altb: |- ( ph -> A < B )
  assume cncfiooiccre.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> RR ) )
  assume cncfiooiccre.l: |- ( ph -> L e. ( F limCC B ) )
  assume cncfiooiccre.r: |- ( ph -> R e. ( F limCC A ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint L x
  disjoint R x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> G e. ( ( A [,] B ) -cn-> RR ) )

  proof
    wph
    cG
    cA
    cB
    cicc
    co
    #
    cr
    ccncf
    co
    wcel
    #
    @0
    cr
    cG
    wf
    #
    wph
    vx
    @0
    vx
    cv
    #
    cA
    wceq
    #
    cR
    @3
    cB
    wceq
    #
    cL
    @3
    cF
    cfv
    #
    cif
    #
    cif
    #
    cr
    cG
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @4
    @8
    cr
    wcel
    #
    wph
    @4
    @11
    @9
    wph
    @4
    wa
    @8
    cR
    cr
    @4
    @8
    cR
    wceq
    wph
    @4
    cR
    @7
    iftrue
    adantl
    wph
    cR
    cr
    wcel
    @4
    wph
    cA
    cB
    cioo
    co
    #
    cA
    cF
    cR
    wph
    cF
    @12
    cr
    ccncf
    co
    #
    wcel
    @12
    cr
    cF
    wf
    #
    cncfiooiccre.f
    @12
    cr
    cF
    cncff
    syl
    #
    @12
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    #
    wph
    cA
    cB
    ccnfld
    ctopn
    cfv
    #
    @17
    eqid
    #
    wph
    cB
    cncfiooiccre.b
    rexrd
    #
    cncfiooiccre.a
    cncfiooiccre.altb
    lptioo1cn
    cncfiooiccre.r
    limcrecl
    adantr
    eqeltrd
    adantlr
    @10
    @4
    wn
    #
    wa
    #
    @5
    @11
    wph
    @20
    @5
    @11
    @9
    wph
    @20
    wa
    @5
    wa
    @8
    cL
    cr
    @20
    @5
    @8
    cL
    wceq
    wph
    @20
    @5
    @8
    @7
    cL
    @4
    cR
    @7
    iffalse
    #
    @5
    cL
    @6
    iftrue
    sylan9eq
    adantll
    wph
    cL
    cr
    wcel
    @20
    @5
    wph
    @12
    cB
    cF
    cL
    @15
    @16
    wph
    cA
    cB
    @17
    @18
    wph
    cA
    cncfiooiccre.a
    rexrd
    #
    cncfiooiccre.b
    cncfiooiccre.altb
    lptioo2cn
    cncfiooiccre.l
    limcrecl
    ad2antrr
    eqeltrd
    adantllr
    @21
    @5
    wn
    #
    wa
    #
    @8
    @6
    cr
    @20
    @24
    @8
    @6
    wceq
    @10
    @20
    @24
    @8
    @7
    @6
    @22
    @5
    cL
    @6
    iffalse
    sylan9eq
    adantll
    @25
    @12
    cr
    @3
    cF
    wph
    @14
    @9
    @20
    @24
    @15
    ad3antrrr
    @25
    cA
    cB
    @3
    wph
    cA
    cxr
    wcel
    #
    @9
    @20
    @24
    @23
    ad3antrrr
    wph
    cB
    cxr
    wcel
    #
    @9
    @20
    @24
    @19
    ad3antrrr
    @10
    @3
    cr
    wcel
    #
    @20
    @24
    @10
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @9
    @28
    wph
    @29
    @9
    cncfiooiccre.a
    adantr
    wph
    @30
    @9
    cncfiooiccre.b
    adantr
    wph
    @9
    simpr
    #
    cA
    cB
    @3
    eliccre
    syl3anc
    #
    ad2antrr
    @21
    cA
    @3
    clt
    wbr
    @24
    @21
    cA
    @3
    wph
    @29
    @9
    @20
    cncfiooiccre.a
    ad2antrr
    @10
    @28
    @20
    @32
    adantr
    @21
    @26
    @27
    @9
    cA
    @3
    cle
    wbr
    wph
    @26
    @9
    @20
    @23
    ad2antrr
    wph
    @27
    @9
    @20
    @19
    ad2antrr
    @10
    @9
    @20
    @31
    adantr
    cA
    cB
    @3
    iccgelb
    syl3anc
    @20
    @3
    cA
    wne
    @10
    @3
    cA
    neqne
    adantl
    leneltd
    adantr
    @10
    @24
    @3
    cB
    clt
    wbr
    @20
    @10
    @24
    wa
    #
    @3
    cB
    @10
    @28
    @24
    @32
    adantr
    wph
    @30
    @9
    @24
    cncfiooiccre.b
    ad2antrr
    @33
    @26
    @27
    @9
    @3
    cB
    cle
    wbr
    wph
    @26
    @9
    @24
    @23
    ad2antrr
    wph
    @27
    @9
    @24
    @19
    ad2antrr
    @10
    @9
    @24
    @31
    adantr
    cA
    cB
    @3
    iccleub
    syl3anc
    @24
    cB
    @3
    wne
    @10
    @24
    @3
    cB
    @3
    cB
    neqne
    necomd
    adantl
    leneltd
    adantlr
    eliood
    ffvelrnd
    eqeltrd
    pm2.61dan
    pm2.61dan
    cncfiooiccre.g
    fmptd
    wph
    cr
    cc
    wss
    #
    cG
    @0
    cc
    ccncf
    co
    wcel
    @1
    @2
    wb
    ax-resscn
    wph
    vx
    cA
    cB
    cR
    cF
    cG
    cL
    cncfiooiccre.x
    cncfiooiccre.g
    cncfiooiccre.a
    cncfiooiccre.b
    wph
    @13
    @12
    cc
    ccncf
    co
    #
    cF
    @34
    cc
    cc
    wss
    @13
    @35
    wss
    ax-resscn
    cc
    ssid
    @12
    cr
    cc
    cncfss
    mp2an
    cncfiooiccre.f
    sseldi
    cncfiooiccre.l
    cncfiooiccre.r
    cncfiooicc
    @0
    cc
    cr
    cG
    cncffvrn
    sylancr
    mpbird
end
