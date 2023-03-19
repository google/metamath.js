include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cram.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "cv.mm"
include "chash.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt2.mm"
include "eqid.mm"
include "simpl1.mm"
include "nnnn0d.mm"
include "simpl2.mm"
include "simpl3.mm"
include "0nn0.mm"
include "a1i.mm"
include "c0.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "simplrl.mm"
include "0elpw.mm"
include "simplrr.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "simpll1.mm"
include "0hashbc.mm"
include "syl.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "fveq2.mm"
include "breq1d.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "sseq2d.mm"
include "anbi12d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "ramub.mm"
include "wb.mm"
include "ramubcl.mm"
include "syl32anc.mm"
include "nn0le0eq0.mm"
include "mpbid.mm"

theorem ramz2
  let cC: class C
  let cR: class R
  let cF: class F
  let cM: class M
  let cV: class V
  let vb: setvar b
  let vd: setvar d
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let va: setvar a
  let vi: setvar i
  let vy: setvar y


  assert |- ( ( ( M e. NN /\ R e. V /\ F : R --> NN0 ) /\ ( C e. R /\ ( F ` C ) = 0 ) ) -> ( M Ramsey F ) = 0 )

  proof
    cM
    cn
    wcel
    #
    cR
    cV
    wcel
    #
    cR
    cn0
    cF
    wf
    #
    w3a
    #
    cC
    cR
    wcel
    #
    cC
    cF
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    wa
    #
    cM
    cF
    cram
    co
    #
    cc0
    cle
    wbr
    #
    @9
    cc0
    wceq
    #
    @8
    vx
    va
    vi
    cvv
    cn0
    vb
    cv
    chash
    cfv
    vi
    cv
    wceq
    vb
    va
    cv
    cpw
    crab
    cmpt2
    #
    cR
    vf
    vi
    cF
    cM
    cc0
    cV
    vs
    va
    vb
    vc
    @12
    eqid
    #
    @8
    cM
    @0
    @1
    @2
    @7
    simpl1
    nnnn0d
    #
    @0
    @1
    @2
    @7
    simpl2
    #
    @0
    @1
    @2
    @7
    simpl3
    #
    cc0
    cn0
    wcel
    #
    @8
    0nn0
    a1i
    #
    @8
    cc0
    vs
    cv
    #
    chash
    cfv
    cle
    wbr
    @19
    cM
    @12
    co
    cR
    vf
    cv
    #
    wf
    wa
    #
    wa
    #
    @4
    c0
    @19
    cpw
    #
    wcel
    #
    @5
    cc0
    cle
    wbr
    #
    c0
    cM
    @12
    co
    #
    @20
    ccnv
    #
    cC
    csn
    #
    cima
    #
    wss
    #
    vc
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @33
    cM
    @12
    co
    #
    @27
    @31
    csn
    #
    cima
    #
    wss
    #
    wa
    #
    vx
    @23
    wrex
    vc
    cR
    wrex
    @3
    @4
    @6
    @21
    simplrl
    @24
    @22
    @19
    0elpw
    a1i
    @22
    @5
    cc0
    cc0
    cle
    @3
    @4
    @6
    @21
    simplrr
    0le0
    syl6eqbr
    @22
    @26
    c0
    @29
    @22
    @0
    @26
    c0
    wceq
    @0
    @1
    @2
    @7
    @21
    simpll1
    @12
    vi
    cM
    va
    vb
    @13
    0hashbc
    syl
    @29
    0ss
    syl6eqss
    @40
    @25
    @30
    wa
    @5
    @34
    cle
    wbr
    #
    @36
    @29
    wss
    #
    wa
    vc
    vx
    cC
    c0
    cR
    @23
    @31
    cC
    wceq
    #
    @35
    @41
    @39
    @42
    @43
    @32
    @5
    @34
    cle
    @31
    cC
    cF
    fveq2
    breq1d
    @43
    @38
    @29
    @36
    @43
    @37
    @28
    @27
    @31
    cC
    sneq
    imaeq2d
    sseq2d
    anbi12d
    @33
    c0
    wceq
    #
    @41
    @25
    @42
    @30
    @44
    @34
    cc0
    @5
    cle
    @44
    @34
    c0
    chash
    cfv
    cc0
    @33
    c0
    chash
    fveq2
    hash0
    syl6eq
    breq2d
    @44
    @36
    @26
    @29
    @33
    c0
    cM
    @12
    oveq1
    sseq1d
    anbi12d
    rspc2ev
    syl112anc
    ramub
    #
    @8
    @9
    cn0
    wcel
    #
    @10
    @11
    wb
    @8
    cM
    cn0
    wcel
    @1
    @2
    @17
    @10
    @46
    @14
    @15
    @16
    @18
    @45
    cc0
    cR
    cF
    cM
    cV
    ramubcl
    syl32anc
    @9
    nn0le0eq0
    syl
    mpbid
end
