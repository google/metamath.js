include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cminusg.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "cghm.mm"
include "wceq.mm"
include "eqid.mm"
include "psgnghm2.mm"
include "ghminv.mm"
include "sylan.mm"
include "symginv.mm"
include "adantl.mm"
include "fveq2d.mm"
include "cinvr.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "csubg.mm"
include "cnmsgnsubg.mm"
include "wf.mm"
include "cnmsgnbas.mm"
include "ghmf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "cvv.mm"
include "wss.mm"
include "cnex.mm"
include "difss.mm"
include "ssexi.mm"
include "wne.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "prssi.mm"
include "mp2an.mm"
include "ressabs.mm"
include "eqcomi.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "invrfval.mm"
include "subginv.mm"
include "sylancr.mm"
include "sseldi.mm"
include "sylib.mm"
include "cnfldinv.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "wo.mm"
include "fvex.mm"
include "elpr.mm"
include "1div1e1.mm"
include "oveq2.mm"
include "id.mm"
include "3eqtr4a.mm"
include "divneg2.mm"
include "mp3an.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "jaoi.mm"
include "sylbi.mm"
include "eqtrd.mm"

theorem psgninv
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cN: class N
  assume psgninv.s: |- S = ( SymGrp ` D )
  assume psgninv.n: |- N = ( pmSgn ` D )
  assume psgninv.p: |- P = ( Base ` S )


  assert |- ( ( D e. Fin /\ F e. P ) -> ( N ` `' F ) = ( N ` F ) )

  proof
    cD
    cfn
    wcel
    #
    cF
    cP
    wcel
    #
    wa
    #
    cF
    ccnv
    #
    cN
    cfv
    #
    c1
    cF
    cN
    cfv
    #
    cdiv
    co
    #
    @5
    @2
    cF
    cS
    cminusg
    cfv
    #
    cfv
    #
    cN
    cfv
    #
    @5
    ccnfld
    cmgp
    cfv
    #
    c1
    c1
    cneg
    #
    cpr
    #
    cress
    co
    #
    cminusg
    cfv
    #
    cfv
    #
    @4
    @6
    @0
    cN
    cS
    @13
    cghm
    co
    wcel
    #
    @1
    @9
    @15
    wceq
    cD
    cS
    @13
    cN
    psgninv.s
    psgninv.n
    @13
    eqid
    #
    psgnghm2
    #
    cP
    cS
    @13
    cN
    @7
    @14
    cF
    psgninv.p
    @7
    eqid
    #
    @14
    eqid
    #
    ghminv
    sylan
    @2
    @8
    @3
    cN
    @1
    @8
    @3
    wceq
    @0
    cD
    cP
    cF
    cS
    @7
    psgninv.s
    psgninv.p
    @19
    symginv
    adantl
    fveq2d
    @2
    @5
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    @15
    @6
    @2
    @12
    @10
    cc
    cc0
    csn
    #
    cdif
    #
    cress
    co
    #
    csubg
    cfv
    wcel
    @5
    @12
    wcel
    #
    @22
    @15
    wceq
    @25
    @25
    eqid
    #
    cnmsgnsubg
    @0
    cP
    @12
    cF
    cN
    @0
    @16
    cP
    @12
    cN
    wf
    @18
    cS
    @13
    cN
    cP
    @12
    psgninv.p
    @13
    @17
    cnmsgnbas
    ghmf
    syl
    ffvelrnda
    #
    @12
    @25
    @13
    @21
    @14
    @5
    @25
    @12
    cress
    co
    #
    @13
    @24
    cvv
    wcel
    @12
    @24
    wss
    #
    @29
    @13
    wceq
    @24
    cc
    cnex
    cc
    @23
    difss
    ssexi
    c1
    @24
    wcel
    #
    @11
    @24
    wcel
    #
    @30
    @31
    c1
    cc
    wcel
    #
    c1
    cc0
    wne
    #
    ax-1cn
    ax-1ne0
    c1
    cc
    cc0
    eldifsn
    mpbir2an
    @32
    @11
    cc
    wcel
    @11
    cc0
    wne
    neg1cn
    neg1ne0
    @11
    cc
    cc0
    eldifsn
    mpbir2an
    c1
    @11
    @24
    prssi
    mp2an
    #
    @24
    @12
    @10
    cvv
    ressabs
    mp2an
    eqcomi
    ccnfld
    @24
    @25
    @21
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @27
    @21
    eqid
    invrfval
    @20
    subginv
    sylancr
    @2
    @5
    cc
    wcel
    @5
    cc0
    wne
    wa
    #
    @22
    @6
    wceq
    @2
    @5
    @24
    wcel
    @36
    @2
    @12
    @24
    @5
    @35
    @28
    sseldi
    @5
    cc
    cc0
    eldifsn
    sylib
    @5
    cnfldinv
    syl
    eqtr3d
    3eqtr3d
    @2
    @26
    @6
    @5
    wceq
    #
    @28
    @26
    @5
    c1
    wceq
    #
    @5
    @11
    wceq
    #
    wo
    @37
    @5
    c1
    @11
    cF
    cN
    fvex
    elpr
    @38
    @37
    @39
    @38
    c1
    c1
    cdiv
    co
    #
    c1
    @6
    @5
    1div1e1
    @5
    c1
    c1
    cdiv
    oveq2
    @38
    id
    3eqtr4a
    @39
    c1
    @11
    cdiv
    co
    #
    @11
    @6
    @5
    @40
    cneg
    #
    @41
    @11
    @33
    @33
    @34
    @42
    @41
    wceq
    ax-1cn
    ax-1cn
    ax-1ne0
    c1
    c1
    divneg2
    mp3an
    @40
    c1
    1div1e1
    negeqi
    eqtr3i
    @5
    @11
    c1
    cdiv
    oveq2
    @39
    id
    3eqtr4a
    jaoi
    sylbi
    syl
    eqtrd
end
