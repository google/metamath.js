include "ccom.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cphtpy.mm"
include "cfv.mm"
include "chtpy.mm"
include "phtpyhtpy.mm"
include "sseldd.mm"
include "htpyco2.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wa.mm"
include "wceq.mm"
include "phtpyi.mm"
include "simpld.mm"
include "fveq2d.mm"
include "cop.mm"
include "cxp.mm"
include "0elunit.mm"
include "simpr.mm"
include "opelxpi.mm"
include "sylancr.mm"
include "cuni.mm"
include "wf.mm"
include "ctx.mm"
include "ctopon.mm"
include "iitopon.mm"
include "txtopon.mm"
include "mp2an.mm"
include "a1i.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "phtpycn.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fvco3.mm"
include "sylan.mm"
include "syldan.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "iiuni.mm"
include "cnf.mm"
include "adantr.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "simprd.mm"
include "1elunit.mm"
include "isphtpyd.mm"

theorem phtpyco2
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let vs: setvar s
  assume phtpyco2.f: |- ( ph -> F e. ( II Cn J ) )
  assume phtpyco2.g: |- ( ph -> G e. ( II Cn J ) )
  assume phtpyco2.p: |- ( ph -> P e. ( J Cn K ) )
  assume phtpyco2.h: |- ( ph -> H e. ( F ( PHtpy ` J ) G ) )


  assert |- ( ph -> ( P o. H ) e. ( ( P o. F ) ( PHtpy ` K ) ( P o. G ) ) )

  proof
    wph
    cP
    cF
    ccom
    #
    cP
    cG
    ccom
    #
    cP
    cH
    ccom
    #
    cK
    vs
    wph
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cP
    cJ
    cK
    ccn
    co
    wcel
    #
    @0
    cii
    cK
    ccn
    co
    #
    wcel
    phtpyco2.f
    phtpyco2.p
    cF
    cP
    cii
    cJ
    cK
    cnco
    syl2anc
    wph
    cG
    @3
    wcel
    @5
    @1
    @6
    wcel
    phtpyco2.g
    phtpyco2.p
    cG
    cP
    cii
    cJ
    cK
    cnco
    syl2anc
    wph
    cP
    cF
    cG
    cH
    cii
    cJ
    cK
    phtpyco2.f
    phtpyco2.g
    phtpyco2.p
    wph
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    #
    cF
    cG
    cii
    cJ
    chtpy
    co
    co
    cH
    wph
    cF
    cG
    cJ
    phtpyco2.f
    phtpyco2.g
    phtpyhtpy
    phtpyco2.h
    sseldd
    htpyco2
    wph
    vs
    cv
    #
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    wa
    #
    cc0
    @8
    cH
    co
    #
    cP
    cfv
    #
    cc0
    cF
    cfv
    #
    cP
    cfv
    #
    cc0
    @8
    @2
    co
    #
    cc0
    @0
    cfv
    #
    @11
    @12
    @14
    cP
    @11
    @12
    @14
    wceq
    #
    c1
    @8
    cH
    co
    #
    c1
    cF
    cfv
    #
    wceq
    #
    wph
    @8
    cF
    cG
    cH
    cJ
    phtpyco2.f
    phtpyco2.g
    phtpyco2.h
    phtpyi
    #
    simpld
    fveq2d
    @11
    cc0
    @8
    cop
    #
    @2
    cfv
    #
    @23
    cH
    cfv
    #
    cP
    cfv
    #
    @16
    @13
    wph
    @10
    @23
    @9
    @9
    cxp
    #
    wcel
    #
    @24
    @26
    wceq
    #
    @11
    cc0
    @9
    wcel
    #
    @10
    @28
    0elunit
    wph
    @10
    simpr
    #
    cc0
    @8
    @9
    @9
    opelxpi
    sylancr
    wph
    @27
    cJ
    cuni
    #
    cH
    wf
    #
    @28
    @29
    wph
    cii
    cii
    ctx
    co
    #
    @27
    ctopon
    cfv
    wcel
    #
    cJ
    @32
    ctopon
    cfv
    wcel
    #
    cH
    @34
    cJ
    ccn
    co
    #
    wcel
    @33
    @35
    wph
    cii
    @9
    ctopon
    cfv
    wcel
    #
    @38
    @35
    iitopon
    iitopon
    cii
    cii
    @9
    @9
    txtopon
    mp2an
    a1i
    wph
    cJ
    ctop
    wcel
    #
    @36
    wph
    @4
    @39
    phtpyco2.f
    cF
    cii
    cJ
    cntop2
    syl
    cJ
    @32
    @32
    eqid
    #
    toptopon
    sylib
    wph
    @7
    @37
    cH
    wph
    cF
    cG
    cJ
    phtpyco2.f
    phtpyco2.g
    phtpycn
    phtpyco2.h
    sseldd
    cH
    @34
    cJ
    @27
    @32
    cnf2
    syl3anc
    #
    @27
    @32
    @23
    cP
    cH
    fvco3
    sylan
    syldan
    cc0
    @8
    @2
    df-ov
    @12
    @25
    cP
    cc0
    @8
    cH
    df-ov
    fveq2i
    3eqtr4g
    @11
    @9
    @32
    cF
    wf
    #
    @30
    @17
    @15
    wceq
    wph
    @42
    @10
    wph
    @4
    @42
    phtpyco2.f
    cF
    cii
    cJ
    @9
    @32
    iiuni
    @40
    cnf
    syl
    adantr
    #
    0elunit
    @9
    @32
    cc0
    cP
    cF
    fvco3
    sylancl
    3eqtr4d
    @11
    @19
    cP
    cfv
    #
    @20
    cP
    cfv
    #
    c1
    @8
    @2
    co
    #
    c1
    @0
    cfv
    #
    @11
    @19
    @20
    cP
    @11
    @18
    @21
    @22
    simprd
    fveq2d
    @11
    c1
    @8
    cop
    #
    @2
    cfv
    #
    @48
    cH
    cfv
    #
    cP
    cfv
    #
    @46
    @44
    wph
    @10
    @48
    @27
    wcel
    #
    @49
    @51
    wceq
    #
    @11
    c1
    @9
    wcel
    #
    @10
    @52
    1elunit
    @31
    c1
    @8
    @9
    @9
    opelxpi
    sylancr
    wph
    @33
    @52
    @53
    @41
    @27
    @32
    @48
    cP
    cH
    fvco3
    sylan
    syldan
    c1
    @8
    @2
    df-ov
    @19
    @50
    cP
    c1
    @8
    cH
    df-ov
    fveq2i
    3eqtr4g
    @11
    @42
    @54
    @47
    @45
    wceq
    @43
    1elunit
    @9
    @32
    c1
    cP
    cF
    fvco3
    sylancl
    3eqtr4d
    isphtpyd
end
