include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cword.mm"
include "wa.mm"
include "cgsu.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "c0g.mm"
include "c0.mm"
include "oveq2.mm"
include "eqid.mm"
include "gsum0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "coeq2.mm"
include "co02.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "wne.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cplusg.mm"
include "cc0.mm"
include "cseq.mm"
include "cmnd.mm"
include "cv.mm"
include "mhmrcl1.mm"
include "ad2antrr.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "cfz.mm"
include "cfzo.mm"
include "wf.mm"
include "wrdf.mm"
include "ad2antlr.mm"
include "cz.mm"
include "cn.mm"
include "cfn.mm"
include "wb.mm"
include "wrdfin.mm"
include "adantl.mm"
include "hashnncl.mm"
include "syl.mm"
include "biimpar.mm"
include "nnzd.mm"
include "fzoval.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffvelrnda.mm"
include "cn0.mm"
include "cuz.mm"
include "nnm1nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "simpll.mm"
include "mhmlin.mm"
include "wfn.mm"
include "ffn.mm"
include "fvco2.mm"
include "eqcomd.mm"
include "seqhomo.mm"
include "gsumval2.mm"
include "cbs.mm"
include "mhmrcl2.mm"
include "mhmf.mm"
include "fco.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "mhm0.mm"
include "adantr.mm"
include "pm2.61ne.mm"

theorem gsumwmhm
  let cB: class B
  let cH: class H
  let cM: class M
  let cN: class N
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume gsumwmhm.b: |- B = ( Base ` M )


  assert |- ( ( H e. ( M MndHom N ) /\ W e. Word B ) -> ( H ` ( M gsum W ) ) = ( N gsum ( H o. W ) ) )

  proof
    cH
    cM
    cN
    cmhm
    co
    wcel
    #
    cW
    cB
    cword
    wcel
    #
    wa
    #
    cM
    cW
    cgsu
    co
    #
    cH
    cfv
    #
    cN
    cH
    cW
    ccom
    #
    cgsu
    co
    #
    wceq
    cM
    c0g
    cfv
    #
    cH
    cfv
    #
    cN
    c0g
    cfv
    #
    wceq
    #
    cW
    c0
    cW
    c0
    wceq
    #
    @4
    @8
    @6
    @9
    @11
    @3
    @7
    cH
    @11
    @3
    cM
    c0
    cgsu
    co
    @7
    cW
    c0
    cM
    cgsu
    oveq2
    cM
    @7
    @7
    eqid
    #
    gsum0
    syl6eq
    fveq2d
    @11
    @6
    cN
    c0
    cgsu
    co
    @9
    @11
    @5
    c0
    cN
    cgsu
    @11
    @5
    cH
    c0
    ccom
    c0
    cW
    c0
    cH
    coeq2
    cH
    co02
    syl6eq
    oveq2d
    cN
    @9
    @9
    eqid
    #
    gsum0
    syl6eq
    eqeq12d
    @2
    cW
    c0
    wne
    #
    wa
    #
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cM
    cplusg
    cfv
    #
    cW
    cc0
    cseq
    cfv
    #
    cH
    cfv
    @17
    cN
    cplusg
    cfv
    #
    @5
    cc0
    cseq
    cfv
    @4
    @6
    @15
    vx
    vy
    @18
    @20
    cB
    cW
    @5
    cH
    cc0
    @17
    @15
    cM
    cmnd
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @22
    @24
    @18
    co
    #
    cB
    wcel
    #
    @0
    @21
    @1
    @14
    cM
    cN
    cH
    mhmrcl1
    ad2antrr
    #
    @21
    @23
    @25
    @28
    cB
    @18
    cM
    @22
    @24
    gsumwmhm.b
    @18
    eqid
    #
    mndcl
    3expb
    sylan
    @15
    cc0
    @17
    cfz
    co
    #
    cB
    @22
    cW
    @15
    cc0
    @16
    cfzo
    co
    #
    cB
    cW
    wf
    #
    @31
    cB
    cW
    wf
    #
    @1
    @33
    @0
    @14
    cB
    cW
    wrdf
    ad2antlr
    @15
    @32
    @31
    cB
    cW
    @15
    @16
    cz
    wcel
    @32
    @31
    wceq
    @15
    @16
    @2
    @16
    cn
    wcel
    #
    @14
    @2
    cW
    cfn
    wcel
    #
    @35
    @14
    wb
    @1
    @36
    @0
    cB
    cW
    wrdfin
    adantl
    cW
    hashnncl
    syl
    biimpar
    #
    nnzd
    cc0
    @16
    fzoval
    syl
    feq2d
    mpbid
    #
    ffvelrnda
    @15
    @17
    cn0
    cc0
    cuz
    cfv
    @15
    @35
    @17
    cn0
    wcel
    @37
    @16
    nnm1nn0
    syl
    nn0uz
    syl6eleq
    #
    @15
    @0
    @26
    @27
    cH
    cfv
    @22
    cH
    cfv
    @24
    cH
    cfv
    @20
    co
    wceq
    #
    @0
    @1
    @14
    simpll
    @0
    @23
    @25
    @40
    cB
    @18
    @20
    cM
    cN
    cH
    @22
    @24
    gsumwmhm.b
    @30
    @20
    eqid
    #
    mhmlin
    3expb
    sylan
    @15
    @22
    @31
    wcel
    #
    wa
    @22
    @5
    cfv
    #
    @22
    cW
    cfv
    cH
    cfv
    #
    @15
    cW
    @31
    wfn
    #
    @42
    @43
    @44
    wceq
    @15
    @34
    @45
    @38
    @31
    cB
    cW
    ffn
    syl
    @31
    cH
    cW
    @22
    fvco2
    sylan
    eqcomd
    seqhomo
    @15
    @3
    @19
    cH
    @15
    cB
    @18
    cW
    cM
    cc0
    @17
    cmnd
    gsumwmhm.b
    @30
    @29
    @39
    @38
    gsumval2
    fveq2d
    @15
    cN
    cbs
    cfv
    #
    @20
    @5
    cN
    cc0
    @17
    cmnd
    @46
    eqid
    #
    @41
    @0
    cN
    cmnd
    wcel
    @1
    @14
    cM
    cN
    cH
    mhmrcl2
    ad2antrr
    @39
    @15
    cB
    @46
    cH
    wf
    #
    @34
    @31
    @46
    @5
    wf
    @0
    @48
    @1
    @14
    cB
    @46
    cM
    cN
    cH
    gsumwmhm.b
    @47
    mhmf
    ad2antrr
    @38
    @31
    cB
    @46
    cH
    cW
    fco
    syl2anc
    gsumval2
    3eqtr4d
    @0
    @10
    @1
    cM
    cN
    cH
    @9
    @7
    @12
    @13
    mhm0
    adantr
    pm2.61ne
end
