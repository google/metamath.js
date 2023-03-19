include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cbl.mm"
include "cfv.mm"
include "crn.mm"
include "wral.mm"
include "wf1o.mm"
include "wceq.mm"
include "cismty.mm"
include "wa.mm"
include "cxmt.mm"
include "wb.mm"
include "isismty.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "f1of.mm"
include "syl.mm"
include "cxr.mm"
include "cxp.mm"
include "adantr.mm"
include "wi.mm"
include "ismtycnv.mm"
include "mpd.mm"
include "simprl.mm"
include "simprr.mm"
include "ismtyima.mm"
include "syl32anc.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "blopn.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "cpw.mm"
include "wfn.mm"
include "blf.mm"
include "ffn.mm"
include "imaeq2.mm"
include "ralrn.mm"
include "4syl.mm"
include "mpbird.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "ctg.mm"
include "mopnval.mm"
include "tgcn.mm"
include "mpbir2and.mm"

theorem ismtyhmeolem
  let wph: wff ph
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  assume ismtyhmeo.1: |- J = ( MetOpen ` M )
  assume ismtyhmeo.2: |- K = ( MetOpen ` N )
  assume ismtyhmeolem.3: |- ( ph -> M e. ( *Met ` X ) )
  assume ismtyhmeolem.4: |- ( ph -> N e. ( *Met ` Y ) )
  assume ismtyhmeolem.5: |- ( ph -> F e. ( M Ismty N ) )


  assert |- ( ph -> F e. ( J Cn K ) )

  proof
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vu
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vu
    cN
    cbl
    cfv
    #
    crn
    #
    wral
    #
    wph
    cX
    cY
    cF
    wf1o
    #
    @0
    wph
    @8
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    @9
    cF
    cfv
    @10
    cF
    cfv
    cN
    co
    wceq
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wph
    cF
    cM
    cN
    cismty
    co
    wcel
    #
    @8
    @11
    wa
    #
    ismtyhmeolem.5
    wph
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    @12
    @13
    wb
    ismtyhmeolem.3
    ismtyhmeolem.4
    vx
    vy
    cF
    cM
    cN
    cX
    cY
    isismty
    syl2anc
    mpbid
    simpld
    #
    cX
    cY
    cF
    f1of
    syl
    wph
    @7
    @1
    vz
    cv
    #
    @5
    cfv
    #
    cima
    #
    cJ
    wcel
    #
    vz
    cY
    cxr
    cxp
    #
    wral
    #
    wph
    @1
    vw
    cv
    #
    vr
    cv
    #
    @5
    co
    #
    cima
    #
    cJ
    wcel
    #
    vr
    cxr
    wral
    vw
    cY
    wral
    @22
    wph
    @27
    vw
    vr
    cY
    cxr
    wph
    @23
    cY
    wcel
    #
    @24
    cxr
    wcel
    #
    wa
    #
    wa
    #
    @26
    @23
    @1
    cfv
    #
    @24
    cM
    cbl
    cfv
    co
    #
    cJ
    @31
    @15
    @14
    @1
    cN
    cM
    cismty
    co
    wcel
    #
    @28
    @29
    @26
    @33
    wceq
    wph
    @15
    @30
    ismtyhmeolem.4
    adantr
    wph
    @14
    @30
    ismtyhmeolem.3
    adantr
    #
    wph
    @34
    @30
    wph
    @12
    @34
    ismtyhmeolem.5
    wph
    @14
    @15
    @12
    @34
    wi
    ismtyhmeolem.3
    ismtyhmeolem.4
    cF
    cM
    cN
    cX
    cY
    ismtycnv
    syl2anc
    mpd
    adantr
    wph
    @28
    @29
    simprl
    wph
    @28
    @29
    simprr
    #
    @23
    @24
    @1
    cN
    cM
    cY
    cX
    ismtyima
    syl32anc
    @31
    @14
    @32
    cX
    wcel
    #
    @29
    @33
    cJ
    wcel
    @35
    wph
    cY
    cX
    @1
    wf
    #
    @28
    @37
    @30
    wph
    @8
    cY
    cX
    @1
    wf1o
    @38
    @16
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @1
    f1of
    3syl
    @28
    @29
    simpl
    cY
    cX
    @23
    @1
    ffvelrn
    syl2an
    @36
    cM
    @32
    @24
    cJ
    cX
    ismtyhmeo.1
    blopn
    syl3anc
    eqeltrd
    ralrimivva
    @20
    @27
    vz
    vw
    vr
    cY
    cxr
    @17
    @23
    @24
    cop
    #
    wceq
    #
    @19
    @26
    cJ
    @40
    @18
    @25
    @1
    @40
    @18
    @39
    @5
    cfv
    @25
    @17
    @39
    @5
    fveq2
    @23
    @24
    @5
    df-ov
    syl6eqr
    imaeq2d
    eleq1d
    ralxp
    sylibr
    wph
    @15
    @21
    cY
    cpw
    #
    @5
    wf
    @5
    @21
    wfn
    @7
    @22
    wb
    ismtyhmeolem.4
    cN
    cY
    blf
    @21
    @41
    @5
    ffn
    @4
    @20
    vu
    vz
    @21
    @5
    @2
    @18
    wceq
    @3
    @19
    cJ
    @2
    @18
    @1
    imaeq2
    eleq1d
    ralrn
    4syl
    mpbird
    wph
    vu
    @6
    cF
    cJ
    cK
    cX
    cY
    wph
    @14
    cJ
    cX
    ctopon
    cfv
    wcel
    ismtyhmeolem.3
    cM
    cJ
    cX
    ismtyhmeo.1
    mopntopon
    syl
    wph
    @15
    cK
    @6
    ctg
    cfv
    wceq
    ismtyhmeolem.4
    cN
    cK
    cY
    ismtyhmeo.2
    mopnval
    syl
    wph
    @15
    cK
    cY
    ctopon
    cfv
    wcel
    ismtyhmeolem.4
    cN
    cK
    cY
    ismtyhmeo.2
    mopntopon
    syl
    tgcn
    mpbir2and
end
