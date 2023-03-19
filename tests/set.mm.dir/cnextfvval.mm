include "wcel.mm"
include "wa.mm"
include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "wfun.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "cuni.mm"
include "wbr.mm"
include "wceq.mm"
include "ctop.mm"
include "cha.mm"
include "wf.mm"
include "wss.mm"
include "adantr.mm"
include "cnextfun.mm"
include "syl22anc.mm"
include "cop.mm"
include "ccl.mm"
include "cv.mm"
include "cxp.mm"
include "ciun.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "fvex.mm"
include "uniex.mm"
include "snid.mm"
include "c1o.mm"
include "cen.mm"
include "wi.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "cfil.mm"
include "c0.mm"
include "wne.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "simpr.mm"
include "w3a.mm"
include "trnei.mm"
include "biimpa.mm"
include "syl31anc.mm"
include "hausflf2.mm"
include "expcom.mm"
include "vtoclga.mm"
include "impcom.mm"
include "en1b.mm"
include "syl5eleqr.mm"
include "wb.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "nfv.mm"
include "nfbi.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "opeliunxp.mm"
include "vtoclg1f.mm"
include "adantl.mm"
include "mpbir2and.mm"
include "df-br.mm"
include "haustop.mm"
include "syl.mm"
include "cnextfval.mm"
include "syl5bb.mm"
include "mpbird.mm"
include "funbrfv.mm"
include "sylc.mm"

theorem cnextfvval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  assume cnextf.1: |- C = U. J
  assume cnextf.2: |- B = U. K
  assume cnextf.3: |- ( ph -> J e. Top )
  assume cnextf.4: |- ( ph -> K e. Haus )
  assume cnextf.5: |- ( ph -> F : A --> B )
  assume cnextf.a: |- ( ph -> A C_ C )
  assume cnextf.6: |- ( ph -> ( ( cls ` J ) ` A ) = C )
  assume cnextf.7: |- ( ( ph /\ x e. C ) -> ( ( K fLimf ( ( ( nei ` J ) ` { x } ) |`t A ) ) ` F ) =/= (/) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint J x
  disjoint K x
  disjoint X x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X y
  disjoint ph y
  assert |- ( ( ph /\ X e. C ) -> ( ( ( J CnExt K ) ` F ) ` X ) = U. ( ( K fLimf ( ( ( nei ` J ) ` { X } ) |`t A ) ) ` F ) )

  proof
    wph
    cX
    cC
    wcel
    #
    wa
    #
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    wfun
    #
    cX
    cF
    cK
    cX
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cuni
    #
    @2
    wbr
    #
    cX
    @2
    cfv
    @10
    wceq
    @1
    cJ
    ctop
    wcel
    #
    cK
    cha
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cA
    cC
    wss
    #
    @3
    wph
    @12
    @0
    cnextf.3
    adantr
    #
    wph
    @13
    @0
    cnextf.4
    adantr
    wph
    @14
    @0
    cnextf.5
    adantr
    #
    wph
    @15
    @0
    cnextf.a
    adantr
    #
    cA
    cB
    cC
    cF
    cJ
    cK
    cnextf.1
    cnextf.2
    cnextfun
    syl22anc
    @1
    @11
    cX
    @10
    cop
    #
    vx
    cA
    cJ
    ccl
    cfv
    cfv
    #
    vx
    cv
    #
    csn
    #
    cF
    cK
    @22
    @5
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cxp
    #
    ciun
    #
    wcel
    #
    @1
    @29
    cX
    @20
    wcel
    #
    @10
    @9
    wcel
    #
    wph
    @30
    @0
    wph
    @20
    cC
    cX
    cnextf.6
    eleq2d
    biimpar
    @1
    @10
    @10
    csn
    #
    @9
    @10
    @9
    cF
    @8
    fvex
    uniex
    snid
    @1
    @9
    c1o
    cen
    wbr
    #
    @9
    @32
    wceq
    @0
    wph
    @33
    wph
    @26
    c1o
    cen
    wbr
    #
    wi
    wph
    @33
    wi
    vx
    cX
    cC
    @21
    cX
    wceq
    #
    @34
    @33
    wph
    @35
    @26
    @9
    c1o
    cen
    @35
    cF
    @25
    @8
    @35
    @24
    @7
    cK
    cflf
    @35
    @23
    @6
    cA
    crest
    @35
    @22
    @4
    @5
    @21
    cX
    sneq
    fveq2d
    oveq1d
    oveq2d
    fveq1d
    #
    breq1d
    imbi2d
    wph
    @21
    cC
    wcel
    #
    @34
    wph
    @37
    wa
    #
    @13
    @24
    cA
    cfil
    cfv
    wcel
    #
    @14
    @26
    c0
    wne
    @34
    wph
    @13
    @37
    cnextf.4
    adantr
    @38
    cJ
    cC
    ctopon
    cfv
    wcel
    #
    @15
    @37
    @21
    @20
    wcel
    #
    @39
    @38
    @12
    @40
    wph
    @12
    @37
    cnextf.3
    adantr
    cJ
    cC
    cnextf.1
    toptopon
    sylib
    wph
    @15
    @37
    cnextf.a
    adantr
    wph
    @37
    simpr
    wph
    @41
    @37
    wph
    @20
    cC
    @21
    cnextf.6
    eleq2d
    biimpar
    @40
    @15
    @37
    w3a
    @41
    @39
    cA
    @21
    cJ
    cC
    trnei
    biimpa
    syl31anc
    wph
    @14
    @37
    cnextf.5
    adantr
    cnextf.7
    cF
    cK
    @24
    cB
    cA
    cnextf.2
    hausflf2
    syl31anc
    expcom
    vtoclga
    impcom
    @9
    en1b
    sylib
    syl5eleqr
    @0
    @29
    @30
    @31
    wa
    #
    wb
    #
    wph
    @21
    @10
    cop
    #
    @28
    wcel
    #
    @41
    @10
    @26
    wcel
    #
    wa
    #
    wb
    @43
    vx
    cX
    cC
    @29
    @42
    vx
    vx
    @19
    @28
    vx
    @20
    @27
    nfiu1
    nfel2
    @42
    vx
    nfv
    nfbi
    @35
    @45
    @29
    @47
    @42
    @35
    @44
    @19
    @28
    @21
    cX
    @10
    opeq1
    eleq1d
    @35
    @41
    @30
    @46
    @31
    @21
    cX
    @20
    eleq1
    @35
    @26
    @9
    @10
    @36
    eleq2d
    anbi12d
    bibi12d
    vx
    @20
    @26
    @10
    opeliunxp
    vtoclg1f
    adantl
    mpbir2and
    @11
    @19
    @2
    wcel
    @1
    @29
    cX
    @10
    @2
    df-br
    @1
    @2
    @28
    @19
    @1
    @12
    cK
    ctop
    wcel
    #
    @14
    @15
    @2
    @28
    wceq
    @16
    wph
    @48
    @0
    wph
    @13
    @48
    cnextf.4
    cK
    haustop
    syl
    adantr
    @17
    @18
    vx
    cA
    cB
    cF
    cJ
    cK
    cC
    cnextf.1
    cnextf.2
    cnextfval
    syl22anc
    eleq2d
    syl5bb
    mpbird
    cX
    @10
    @2
    funbrfv
    sylc
end
