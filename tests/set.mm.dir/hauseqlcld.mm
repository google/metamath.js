include "cin.mm"
include "cdm.mm"
include "cuni.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "cima.mm"
include "ccld.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "biantrud.mm"
include "wbr.mm"
include "fvex.mm"
include "ideq.mm"
include "df-br.mm"
include "bitr3i.mm"
include "opelres.mm"
include "3bitr4g.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "crab.mm"
include "wfn.mm"
include "ffn.mm"
include "fndmin.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "wb.mm"
include "fnmpti.mm"
include "elpreima.mm"
include "mp1i.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "ctx.mm"
include "txcnmpt.mm"
include "cha.mm"
include "ctop.mm"
include "hausdiag.mm"
include "simprbi.mm"
include "cnclima.mm"
include "eqeltrd.mm"

theorem hauseqlcld
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vb: setvar b
  assume hauseqlcld.k: |- ( ph -> K e. Haus )
  assume hauseqlcld.f: |- ( ph -> F e. ( J Cn K ) )
  assume hauseqlcld.g: |- ( ph -> G e. ( J Cn K ) )


  assert |- ( ph -> dom ( F i^i G ) e. ( Clsd ` J ) )

  proof
    wph
    cF
    cG
    cin
    cdm
    #
    va
    cJ
    cuni
    #
    va
    cv
    #
    cF
    cfv
    #
    @2
    cG
    cfv
    #
    cop
    #
    cmpt
    #
    ccnv
    cid
    cK
    cuni
    #
    cres
    #
    cima
    #
    cJ
    ccld
    cfv
    #
    wph
    vb
    @0
    @9
    wph
    vb
    cv
    #
    @1
    wcel
    #
    @11
    cF
    cfv
    #
    @11
    cG
    cfv
    #
    wceq
    #
    wa
    #
    @12
    @11
    @6
    cfv
    #
    @8
    wcel
    #
    wa
    #
    @11
    @0
    wcel
    #
    @11
    @9
    wcel
    #
    wph
    @12
    @15
    @18
    wph
    @12
    wa
    #
    @15
    @13
    @14
    cop
    #
    @8
    wcel
    #
    @18
    @22
    @23
    cid
    wcel
    #
    @25
    @13
    @7
    wcel
    #
    wa
    @15
    @24
    @22
    @26
    @25
    wph
    @1
    @7
    @11
    cF
    wph
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    @1
    @7
    cF
    wf
    #
    hauseqlcld.f
    cF
    cJ
    cK
    @1
    @7
    @1
    eqid
    #
    @7
    eqid
    #
    cnf
    syl
    #
    ffvelrnda
    biantrud
    @15
    @13
    @14
    cid
    wbr
    @25
    @13
    @14
    @11
    cG
    fvex
    #
    ideq
    @13
    @14
    cid
    df-br
    bitr3i
    @13
    @14
    cid
    @7
    @33
    opelres
    3bitr4g
    @22
    @17
    @23
    @8
    @12
    @17
    @23
    wceq
    wph
    va
    @11
    @5
    @23
    @1
    @6
    @2
    @11
    wceq
    @3
    @13
    @4
    @14
    @2
    @11
    cF
    fveq2
    @2
    @11
    cG
    fveq2
    opeq12d
    @6
    eqid
    #
    @13
    @14
    opex
    fvmpt
    adantl
    eleq1d
    bitr4d
    pm5.32da
    wph
    @20
    @11
    @15
    vb
    @1
    crab
    #
    wcel
    @16
    wph
    @0
    @35
    @11
    wph
    cF
    @1
    wfn
    #
    cG
    @1
    wfn
    #
    @0
    @35
    wceq
    wph
    @29
    @36
    @32
    @1
    @7
    cF
    ffn
    syl
    wph
    @1
    @7
    cG
    wf
    #
    @37
    wph
    cG
    @27
    wcel
    #
    @38
    hauseqlcld.g
    cG
    cJ
    cK
    @1
    @7
    @30
    @31
    cnf
    syl
    @1
    @7
    cG
    ffn
    syl
    vb
    @1
    cF
    cG
    fndmin
    syl2anc
    eleq2d
    @15
    vb
    @1
    rabid
    syl6bb
    @6
    @1
    wfn
    @21
    @19
    wb
    wph
    va
    @1
    @5
    @6
    @3
    @4
    opex
    @34
    fnmpti
    @1
    @11
    @8
    @6
    elpreima
    mp1i
    3bitr4d
    eqrdv
    wph
    @6
    cJ
    cK
    cK
    ctx
    co
    #
    ccn
    co
    wcel
    #
    @8
    @40
    ccld
    cfv
    wcel
    #
    @9
    @10
    wcel
    wph
    @28
    @39
    @41
    hauseqlcld.f
    hauseqlcld.g
    va
    cK
    cK
    cJ
    cF
    cG
    @6
    @1
    @30
    @34
    txcnmpt
    syl2anc
    wph
    cK
    cha
    wcel
    #
    @42
    hauseqlcld.k
    @43
    cK
    ctop
    wcel
    @42
    cK
    @7
    @31
    hausdiag
    simprbi
    syl
    @8
    @6
    cJ
    @40
    cnclima
    syl2anc
    eqeltrd
end
