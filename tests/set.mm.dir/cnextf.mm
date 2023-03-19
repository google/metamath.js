include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "ctop.mm"
include "wcel.mm"
include "cha.mm"
include "cnextfun.mm"
include "syl22anc.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "cab.mm"
include "wa.mm"
include "ccl.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "simpl.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "cxp.mm"
include "ciun.mm"
include "haustop.mm"
include "syl.mm"
include "cnextfval.mm"
include "opeliunxp.mm"
include "syl6bb.mm"
include "exbidv.mm"
include "19.42v.mm"
include "syl12anc.mm"
include "simprbda.mm"
include "wb.mm"
include "adantr.mm"
include "mpbid.mm"
include "impbida.mm"
include "abbi2dv.mm"
include "dfdm3.mm"
include "syl6reqr.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "rneqd.mm"
include "rniun.mm"
include "wral.mm"
include "vex.mm"
include "snnz.mm"
include "rnxp.mm"
include "ax-mp.mm"
include "biimpa.mm"
include "ctopon.mm"
include "cfil.mm"
include "toptopon.mm"
include "simpr.mm"
include "w3a.mm"
include "trnei.mm"
include "syl31anc.mm"
include "flfelbas.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl3anc.mm"
include "syldan.mm"
include "syl5eqss.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "df-f.mm"

theorem cnextf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vy: setvar y
  let cX: class X
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
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint ph y
  assert |- ( ph -> ( ( J CnExt K ) ` F ) : C --> B )

  proof
    wph
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    cC
    wfn
    #
    @0
    crn
    #
    cB
    wss
    cC
    cB
    @0
    wf
    wph
    @0
    wfun
    #
    @0
    cdm
    #
    cC
    wceq
    @1
    wph
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
    cnextf.3
    cnextf.4
    cnextf.5
    cnextf.a
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
    wph
    cC
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    #
    vy
    wex
    #
    vx
    cab
    @4
    wph
    @13
    vx
    cC
    wph
    @9
    cC
    wcel
    #
    @13
    wph
    @14
    wa
    #
    wph
    @9
    cA
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @10
    cF
    cK
    @9
    csn
    #
    cJ
    cnei
    cfv
    cfv
    cA
    crest
    co
    #
    cflf
    co
    cfv
    #
    wcel
    #
    vy
    wex
    #
    @13
    wph
    @14
    simpl
    wph
    @17
    @14
    wph
    @16
    cC
    @9
    cnextf.6
    eleq2d
    #
    biimpar
    #
    @15
    @20
    c0
    wne
    @22
    cnextf.7
    vy
    @20
    n0
    sylib
    wph
    @13
    @17
    @22
    wa
    #
    wph
    @13
    @17
    @21
    wa
    #
    vy
    wex
    @25
    wph
    @12
    @26
    vy
    wph
    @12
    @11
    vx
    @16
    @18
    @20
    cxp
    #
    ciun
    #
    wcel
    @26
    wph
    @0
    @28
    @11
    wph
    @5
    cK
    ctop
    wcel
    #
    @7
    @8
    @0
    @28
    wceq
    cnextf.3
    wph
    @6
    @29
    cnextf.4
    cK
    haustop
    syl
    #
    cnextf.5
    cnextf.a
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
    #
    eleq2d
    vx
    @16
    @20
    @10
    opeliunxp
    syl6bb
    exbidv
    @17
    @21
    vy
    19.42v
    syl6bb
    #
    biimpar
    syl12anc
    wph
    @13
    wa
    @17
    @14
    wph
    @13
    @17
    @22
    @32
    simprbda
    wph
    @17
    @14
    wb
    @13
    @23
    adantr
    mpbid
    impbida
    abbi2dv
    vx
    vy
    @0
    dfdm3
    syl6reqr
    @0
    cC
    df-fn
    sylanbrc
    wph
    @2
    @28
    crn
    #
    cB
    wph
    @0
    @28
    @31
    rneqd
    wph
    @33
    vx
    @16
    @27
    crn
    #
    ciun
    #
    cB
    vx
    @16
    @27
    rniun
    wph
    @34
    cB
    wss
    #
    vx
    @16
    wral
    @35
    cB
    wss
    wph
    @36
    vx
    @16
    wph
    @17
    wa
    @34
    @20
    cB
    @18
    c0
    wne
    @34
    @20
    wceq
    @9
    vx
    vex
    snnz
    @18
    @20
    rnxp
    ax-mp
    wph
    @17
    @14
    @20
    cB
    wss
    #
    wph
    @17
    @14
    @23
    biimpa
    @15
    cK
    cB
    ctopon
    cfv
    wcel
    #
    @19
    cA
    cfil
    cfv
    wcel
    #
    @7
    @37
    wph
    @38
    @14
    wph
    @29
    @38
    @30
    cK
    cB
    cnextf.2
    toptopon
    sylib
    adantr
    @15
    cJ
    cC
    ctopon
    cfv
    wcel
    #
    @8
    @14
    @17
    @39
    wph
    @40
    @14
    wph
    @5
    @40
    cnextf.3
    cJ
    cC
    cnextf.1
    toptopon
    sylib
    adantr
    wph
    @8
    @14
    cnextf.a
    adantr
    wph
    @14
    simpr
    @24
    @40
    @8
    @14
    w3a
    @17
    @39
    cA
    @9
    cJ
    cC
    trnei
    biimpa
    syl31anc
    wph
    @7
    @14
    cnextf.5
    adantr
    @38
    @39
    @7
    w3a
    #
    vy
    @20
    cB
    @41
    @21
    @10
    cB
    wcel
    @10
    cF
    cK
    @19
    cB
    cA
    flfelbas
    ex
    ssrdv
    syl3anc
    syldan
    syl5eqss
    ralrimiva
    vx
    @16
    @34
    cB
    iunss
    sylibr
    syl5eqss
    eqsstrd
    cC
    cB
    @0
    df-f
    sylanbrc
end
