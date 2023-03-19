include "ccom.mm"
include "cuni.mm"
include "ctop.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "cntop1.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cii.mm"
include "ctx.mm"
include "chtpy.mm"
include "htpycn.mm"
include "sseldd.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "htpyi.mm"
include "simpld.mm"
include "fveq2d.mm"
include "cop.mm"
include "cicc.mm"
include "cxp.mm"
include "simpr.mm"
include "0elunit.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "wf.mm"
include "iitopon.mm"
include "txtopon.mm"
include "cntop2.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fvco3.mm"
include "sylan.mm"
include "syldan.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "cnf.mm"
include "3eqtr4d.mm"
include "simprd.mm"
include "1elunit.mm"
include "ishtpyd.mm"

theorem htpyco2
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let vs: setvar s
  assume htpyco2.f: |- ( ph -> F e. ( J Cn K ) )
  assume htpyco2.g: |- ( ph -> G e. ( J Cn K ) )
  assume htpyco2.p: |- ( ph -> P e. ( K Cn L ) )
  assume htpyco2.h: |- ( ph -> H e. ( F ( J Htpy K ) G ) )


  assert |- ( ph -> ( P o. H ) e. ( ( P o. F ) ( J Htpy L ) ( P o. G ) ) )

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
    cJ
    cL
    cJ
    cuni
    #
    vs
    wph
    cJ
    ctop
    wcel
    #
    cJ
    @3
    ctopon
    cfv
    wcel
    #
    wph
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    @4
    htpyco2.f
    cF
    cJ
    cK
    cntop1
    syl
    cJ
    @3
    @3
    eqid
    #
    toptopon
    sylib
    #
    wph
    @7
    cP
    cK
    cL
    ccn
    co
    wcel
    #
    @0
    cJ
    cL
    ccn
    co
    #
    wcel
    htpyco2.f
    htpyco2.p
    cF
    cP
    cJ
    cK
    cL
    cnco
    syl2anc
    wph
    cG
    @6
    wcel
    #
    @10
    @1
    @11
    wcel
    htpyco2.g
    htpyco2.p
    cG
    cP
    cJ
    cK
    cL
    cnco
    syl2anc
    wph
    cH
    cJ
    cii
    ctx
    co
    #
    cK
    ccn
    co
    #
    wcel
    #
    @10
    @2
    @13
    cL
    ccn
    co
    wcel
    wph
    cF
    cG
    cJ
    cK
    chtpy
    co
    co
    @14
    cH
    wph
    cF
    cG
    cJ
    cK
    @3
    @9
    htpyco2.f
    htpyco2.g
    htpycn
    htpyco2.h
    sseldd
    #
    htpyco2.p
    cH
    cP
    @13
    cK
    cL
    cnco
    syl2anc
    wph
    vs
    cv
    #
    @3
    wcel
    #
    wa
    #
    @17
    cc0
    cH
    co
    #
    cP
    cfv
    #
    @17
    cF
    cfv
    #
    cP
    cfv
    #
    @17
    cc0
    @2
    co
    #
    @17
    @0
    cfv
    #
    @19
    @20
    @22
    cP
    @19
    @20
    @22
    wceq
    #
    @17
    c1
    cH
    co
    #
    @17
    cG
    cfv
    #
    wceq
    #
    wph
    @17
    cF
    cG
    cH
    cJ
    cK
    @3
    @9
    htpyco2.f
    htpyco2.g
    htpyco2.h
    htpyi
    #
    simpld
    fveq2d
    @19
    @17
    cc0
    cop
    #
    @2
    cfv
    #
    @31
    cH
    cfv
    #
    cP
    cfv
    #
    @24
    @21
    wph
    @18
    @31
    @3
    cc0
    c1
    cicc
    co
    #
    cxp
    #
    wcel
    #
    @32
    @34
    wceq
    #
    @19
    @18
    cc0
    @35
    wcel
    @37
    wph
    @18
    simpr
    #
    0elunit
    @17
    cc0
    @3
    @35
    opelxpi
    sylancl
    wph
    @36
    cK
    cuni
    #
    cH
    wf
    #
    @37
    @38
    wph
    @13
    @36
    ctopon
    cfv
    wcel
    #
    cK
    @40
    ctopon
    cfv
    wcel
    #
    @15
    @41
    wph
    @5
    cii
    @35
    ctopon
    cfv
    wcel
    @42
    @9
    iitopon
    cJ
    cii
    @3
    @35
    txtopon
    sylancl
    wph
    cK
    ctop
    wcel
    #
    @43
    wph
    @7
    @44
    htpyco2.f
    cF
    cJ
    cK
    cntop2
    syl
    cK
    @40
    @40
    eqid
    #
    toptopon
    sylib
    @16
    cH
    @13
    cK
    @36
    @40
    cnf2
    syl3anc
    #
    @36
    @40
    @31
    cP
    cH
    fvco3
    sylan
    syldan
    @17
    cc0
    @2
    df-ov
    @20
    @33
    cP
    @17
    cc0
    cH
    df-ov
    fveq2i
    3eqtr4g
    wph
    @3
    @40
    cF
    wf
    #
    @18
    @25
    @23
    wceq
    wph
    @7
    @47
    htpyco2.f
    cF
    cJ
    cK
    @3
    @40
    @8
    @45
    cnf
    syl
    @3
    @40
    @17
    cP
    cF
    fvco3
    sylan
    3eqtr4d
    @19
    @27
    cP
    cfv
    #
    @28
    cP
    cfv
    #
    @17
    c1
    @2
    co
    #
    @17
    @1
    cfv
    #
    @19
    @27
    @28
    cP
    @19
    @26
    @29
    @30
    simprd
    fveq2d
    @19
    @17
    c1
    cop
    #
    @2
    cfv
    #
    @52
    cH
    cfv
    #
    cP
    cfv
    #
    @50
    @48
    wph
    @18
    @52
    @36
    wcel
    #
    @53
    @55
    wceq
    #
    @19
    @18
    c1
    @35
    wcel
    @56
    @39
    1elunit
    @17
    c1
    @3
    @35
    opelxpi
    sylancl
    wph
    @41
    @56
    @57
    @46
    @36
    @40
    @52
    cP
    cH
    fvco3
    sylan
    syldan
    @17
    c1
    @2
    df-ov
    @27
    @54
    cP
    @17
    c1
    cH
    df-ov
    fveq2i
    3eqtr4g
    wph
    @3
    @40
    cG
    wf
    #
    @18
    @51
    @49
    wceq
    wph
    @12
    @58
    htpyco2.g
    cG
    cJ
    cK
    @3
    @40
    @8
    @45
    cnf
    syl
    @3
    @40
    @17
    cP
    cG
    fvco3
    sylan
    3eqtr4d
    ishtpyd
end
