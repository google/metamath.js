include "cnv.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "cba.mm"
include "cfv.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "eqid.mm"
include "nvf.mm"
include "wa.mm"
include "simprr.mm"
include "cle.mm"
include "w3a.mm"
include "nvcl.mm"
include "ex.mm"
include "anim12d.mm"
include "cme.mm"
include "remet.mm"
include "metcl.mm"
include "mp3an1.mm"
include "syl6.mm"
include "3impib.mm"
include "imsmet.mm"
include "syl3an1.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cpv.mm"
include "nvabs.mm"
include "wceq.mm"
include "remetdval.mm"
include "syl.mm"
include "imsdval2.mm"
include "3brtr4d.mm"
include "jca31.mm"
include "3expa.mm"
include "rpre.mm"
include "lelttr.mm"
include "expdimp.mm"
include "an32s.mm"
include "syl2an.mm"
include "ralrimdva.mm"
include "impr.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "wb.mm"
include "imsxmet.mm"
include "rexmet.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cmopn.mm"
include "tgioo.mm"
include "eqtri.mm"
include "metcn.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem nmcvcn
  let cC: class C
  let cU: class U
  let cJ: class J
  let cK: class K
  let cN: class N
  let vd: setvar d
  let ve: setvar e
  let vx: setvar x
  let vy: setvar y
  assume nmcvcn.1: |- N = ( normCV ` U )
  assume nmcvcn.2: |- C = ( IndMet ` U )
  assume nmcvcn.j: |- J = ( MetOpen ` C )
  assume nmcvcn.k: |- K = ( topGen ` ran (,) )


  assert |- ( U e. NrmCVec -> N e. ( J Cn K ) )

  proof
    cU
    cnv
    wcel
    #
    cN
    cJ
    cK
    ccn
    co
    wcel
    #
    cU
    cba
    cfv
    #
    cr
    cN
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cC
    co
    #
    vd
    cv
    #
    clt
    wbr
    #
    @4
    cN
    cfv
    #
    @5
    cN
    cfv
    #
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    co
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    @2
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    vx
    @2
    wral
    #
    cU
    cN
    @2
    @2
    eqid
    #
    nmcvcn.1
    nvf
    @0
    @17
    vx
    ve
    @2
    crp
    @0
    @4
    @2
    wcel
    #
    @13
    crp
    wcel
    #
    wa
    wa
    @21
    @6
    @13
    clt
    wbr
    #
    @14
    wi
    #
    vy
    @2
    wral
    #
    @17
    @0
    @20
    @21
    simprr
    @0
    @20
    @21
    @24
    @0
    @20
    wa
    #
    @21
    @23
    vy
    @2
    @25
    @5
    @2
    wcel
    #
    wa
    #
    @21
    @23
    @27
    @12
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    #
    @12
    @6
    cle
    wbr
    #
    wa
    #
    @13
    cr
    wcel
    #
    @23
    @21
    @0
    @20
    @26
    @32
    @0
    @20
    @26
    w3a
    #
    @28
    @29
    @31
    @0
    @20
    @26
    @28
    @0
    @20
    @26
    wa
    @9
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    wa
    #
    @28
    @0
    @20
    @35
    @26
    @36
    @0
    @20
    @35
    @4
    cU
    cN
    @2
    @19
    nmcvcn.1
    nvcl
    ex
    @0
    @26
    @36
    @5
    cU
    cN
    @2
    @19
    nmcvcn.1
    nvcl
    ex
    anim12d
    #
    @11
    cr
    cme
    cfv
    wcel
    @35
    @36
    @28
    @11
    @11
    eqid
    #
    remet
    @9
    @10
    @11
    cr
    metcl
    mp3an1
    syl6
    3impib
    @0
    cC
    @2
    cme
    cfv
    wcel
    @20
    @26
    @29
    cC
    cU
    @2
    @19
    nmcvcn.2
    imsmet
    @4
    @5
    cC
    @2
    metcl
    syl3an1
    @34
    @9
    @10
    cmin
    co
    cabs
    cfv
    #
    @4
    c1
    cneg
    @5
    cU
    cns
    cfv
    #
    co
    cU
    cpv
    cfv
    #
    co
    cN
    cfv
    @12
    @6
    cle
    @4
    @5
    @41
    cU
    @42
    cN
    @2
    @19
    @42
    eqid
    #
    @41
    eqid
    #
    nmcvcn.1
    nvabs
    @34
    @37
    @12
    @40
    wceq
    @0
    @20
    @26
    @37
    @38
    3impib
    @9
    @10
    @11
    @39
    remetdval
    syl
    @4
    @5
    cC
    @41
    cU
    @42
    cN
    @2
    @19
    @43
    @44
    nmcvcn.1
    nmcvcn.2
    imsdval2
    3brtr4d
    jca31
    3expa
    @13
    rpre
    @30
    @33
    @31
    @23
    @30
    @33
    wa
    @31
    @22
    @14
    @28
    @29
    @33
    @31
    @22
    wa
    @14
    wi
    @12
    @6
    @13
    lelttr
    3expa
    expdimp
    an32s
    syl2an
    ex
    ralrimdva
    impr
    @16
    @24
    vd
    @13
    crp
    @7
    @13
    wceq
    #
    @15
    @23
    vy
    @2
    @45
    @8
    @22
    @14
    @7
    @13
    @6
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    @0
    cC
    @2
    cxmt
    cfv
    wcel
    @11
    cr
    cxmt
    cfv
    wcel
    @1
    @3
    @18
    wa
    wb
    cC
    cU
    @2
    @19
    nmcvcn.2
    imsxmet
    @11
    @39
    rexmet
    vx
    ve
    vd
    vy
    cC
    @11
    cN
    cJ
    cK
    @2
    cr
    nmcvcn.j
    cK
    cioo
    crn
    ctg
    cfv
    @11
    cmopn
    cfv
    #
    nmcvcn.k
    @11
    @46
    @39
    @46
    eqid
    tgioo
    eqtri
    metcn
    sylancl
    mpbir2and
end
