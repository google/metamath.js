include "cufl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cfil.mm"
include "wral.mm"
include "cfg.mm"
include "co.mm"
include "simpll.mm"
include "cfbas.mm"
include "cpw.mm"
include "filfbas.mm"
include "adantl.mm"
include "filsspw.mm"
include "simplr.mm"
include "sspwb.mm"
include "sylib.mm"
include "sstrd.mm"
include "fbasweak.mm"
include "syl3anc.mm"
include "fgcl.mm"
include "syl.mm"
include "ufli.mm"
include "syl2anc.mm"
include "crest.mm"
include "ssfg.mm"
include "adantr.mm"
include "simprr.mm"
include "filtop.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "wb.mm"
include "simprl.mm"
include "trufil.mm"
include "mpbird.mm"
include "wceq.mm"
include "restid2.mm"
include "ssrest.mm"
include "eqsstr3d.mm"
include "sseq2.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "ssexg.mm"
include "ancoms.mm"
include "isufl.mm"

theorem ssufl
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vu: setvar u
  let vx: setvar x


  assert |- ( ( X e. UFL /\ Y C_ X ) -> Y e. UFL )

  proof
    cX
    cufl
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    cY
    cufl
    wcel
    #
    vf
    cv
    #
    vg
    cv
    #
    wss
    #
    vg
    cY
    cufil
    cfv
    #
    wrex
    #
    vf
    cY
    cfil
    cfv
    #
    wral
    #
    @2
    @8
    vf
    @9
    @2
    @4
    @9
    wcel
    #
    wa
    #
    cX
    @4
    cfg
    co
    #
    vu
    cv
    #
    wss
    #
    @8
    vu
    cX
    cufil
    cfv
    #
    @12
    @0
    @13
    cX
    cfil
    cfv
    wcel
    #
    @15
    vu
    @16
    wrex
    @0
    @1
    @11
    simpll
    #
    @12
    @4
    cX
    cfbas
    cfv
    wcel
    #
    @17
    @12
    @4
    cY
    cfbas
    cfv
    wcel
    #
    @4
    cX
    cpw
    #
    wss
    @0
    @19
    @11
    @20
    @2
    @4
    cY
    filfbas
    adantl
    @12
    @4
    cY
    cpw
    #
    @21
    @11
    @4
    @22
    wss
    #
    @2
    @4
    cY
    filsspw
    adantl
    #
    @12
    @1
    @22
    @21
    wss
    @0
    @1
    @11
    simplr
    #
    cY
    cX
    sspwb
    sylib
    sstrd
    @18
    @4
    cufl
    cY
    cX
    fbasweak
    syl3anc
    #
    @4
    cX
    fgcl
    syl
    vu
    @13
    cX
    ufli
    syl2anc
    @12
    @14
    @16
    wcel
    #
    @15
    wa
    #
    wa
    #
    @14
    cY
    crest
    co
    #
    @7
    wcel
    #
    @4
    @30
    wss
    #
    @8
    @29
    @31
    cY
    @14
    wcel
    #
    @29
    @4
    @14
    cY
    @29
    @4
    @13
    @14
    @12
    @4
    @13
    wss
    #
    @28
    @12
    @19
    @34
    @26
    @4
    cX
    ssfg
    syl
    adantr
    @12
    @27
    @15
    simprr
    sstrd
    #
    @11
    cY
    @4
    wcel
    #
    @2
    @28
    @4
    cY
    filtop
    ad2antlr
    #
    sseldd
    @29
    @27
    @1
    @31
    @33
    wb
    @12
    @27
    @15
    simprl
    #
    @12
    @1
    @28
    @25
    adantr
    cY
    @14
    cX
    trufil
    syl2anc
    mpbird
    @29
    @4
    @4
    cY
    crest
    co
    #
    @30
    @29
    @36
    @23
    @39
    @4
    wceq
    @37
    @12
    @23
    @28
    @24
    adantr
    cY
    @4
    @4
    restid2
    syl2anc
    @29
    @27
    @4
    @14
    wss
    @39
    @30
    wss
    @38
    @35
    cY
    @4
    @14
    @16
    ssrest
    syl2anc
    eqsstr3d
    @6
    @32
    vg
    @30
    @7
    @5
    @30
    @4
    sseq2
    rspcev
    syl2anc
    rexlimddv
    ralrimiva
    @2
    cY
    cvv
    wcel
    #
    @3
    @10
    wb
    @1
    @0
    @40
    cY
    cX
    cufl
    ssexg
    ancoms
    vf
    vg
    cvv
    cY
    isufl
    syl
    mpbird
end
