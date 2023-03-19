include "crn.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cres.mm"
include "cun.mm"
include "cfn.mm"
include "imaundi.mm"
include "reseq2i.mm"
include "undif1.mm"
include "wss.mm"
include "wceq.mm"
include "ssv.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "eqtri.mm"
include "imaeq2i.mm"
include "resundi.mm"
include "3eqtr3i.mm"
include "wfun.mm"
include "cdm.mm"
include "dfdm4.mm"
include "dfrn4.mm"
include "wa.mm"
include "wfn.mm"
include "df-fn.mm"
include "fnresdm.mm"
include "sylbir.mm"
include "sylancl.mm"
include "syl5reqr.mm"
include "rneqd.mm"
include "rnun.mm"
include "syl6eq.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "suppimacnv.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "3syl.mm"
include "wfo.mm"
include "cnvimass.mm"
include "fores.mm"
include "fofn.mm"
include "syl.mm"
include "fnrndomg.mm"
include "sylc.mm"
include "domfi.mm"
include "snfi.mm"
include "cin.mm"
include "df-ima.mm"
include "funimacnv.mm"
include "syl5eqr.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "ssfi.mm"
include "sylancr.mm"
include "unfi.mm"
include "eqeltrd.mm"

theorem ffsrn
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume ffsrn.z: |- ( ph -> Z e. W )
  assume ffsrn.0: |- ( ph -> F e. V )
  assume ffsrn.1: |- ( ph -> Fun F )
  assume ffsrn.2: |- ( ph -> ( F supp Z ) e. Fin )


  assert |- ( ph -> ran F e. Fin )

  proof
    wph
    cF
    crn
    #
    cF
    cF
    ccnv
    #
    cvv
    cZ
    csn
    #
    cdif
    #
    cima
    #
    cres
    #
    crn
    #
    cF
    @1
    @2
    cima
    #
    cres
    #
    crn
    #
    cun
    #
    cfn
    wph
    @0
    @5
    @8
    cun
    #
    crn
    @10
    wph
    cF
    @11
    wph
    @11
    cF
    @1
    cvv
    cima
    #
    cres
    #
    cF
    cF
    @1
    @3
    @2
    cun
    #
    cima
    #
    cres
    cF
    @4
    @7
    cun
    #
    cres
    @13
    @11
    @15
    @16
    cF
    @1
    @3
    @2
    imaundi
    reseq2i
    @15
    @12
    cF
    @14
    cvv
    @1
    @14
    cvv
    @2
    cun
    #
    cvv
    cvv
    @2
    undif1
    @2
    cvv
    wss
    @17
    cvv
    wceq
    @2
    ssv
    @2
    cvv
    ssequn2
    mpbi
    eqtri
    imaeq2i
    reseq2i
    cF
    @4
    @7
    resundi
    3eqtr3i
    wph
    cF
    wfun
    #
    cF
    cdm
    #
    @12
    wceq
    #
    @13
    cF
    wceq
    #
    ffsrn.1
    @19
    @1
    crn
    @12
    cF
    dfdm4
    @1
    dfrn4
    eqtri
    @18
    @20
    wa
    cF
    @12
    wfn
    @21
    cF
    @12
    df-fn
    @12
    cF
    fnresdm
    sylbir
    sylancl
    syl5reqr
    rneqd
    @5
    @8
    rnun
    syl6eq
    wph
    @6
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    @10
    cfn
    wcel
    wph
    @4
    cfn
    wcel
    @6
    @4
    cdom
    wbr
    #
    @22
    wph
    cF
    cZ
    csupp
    co
    #
    @4
    cfn
    wph
    cF
    cV
    wcel
    #
    cZ
    cW
    wcel
    @25
    @4
    wceq
    ffsrn.0
    ffsrn.z
    cF
    cV
    cW
    cZ
    suppimacnv
    syl2anc
    ffsrn.2
    eqeltrrd
    wph
    @4
    cvv
    wcel
    #
    @5
    @4
    wfn
    #
    @24
    wph
    @26
    @1
    cvv
    wcel
    @27
    ffsrn.0
    cF
    cV
    cnvexg
    @1
    @3
    cvv
    imaexg
    3syl
    wph
    @4
    cF
    @4
    cima
    #
    @5
    wfo
    #
    @28
    wph
    @18
    @4
    @19
    wss
    @30
    ffsrn.1
    cF
    @3
    cnvimass
    @4
    cF
    fores
    sylancl
    @4
    @29
    @5
    fofn
    syl
    @4
    cvv
    @5
    fnrndomg
    sylc
    @4
    @6
    domfi
    syl2anc
    wph
    @2
    cfn
    wcel
    @9
    @2
    wss
    @23
    cZ
    snfi
    wph
    @9
    @2
    @0
    cin
    #
    @2
    wph
    @9
    cF
    @7
    cima
    #
    @31
    cF
    @7
    df-ima
    wph
    @18
    @32
    @31
    wceq
    ffsrn.1
    @2
    cF
    funimacnv
    syl
    syl5eqr
    @2
    @0
    inss1
    syl6eqss
    @2
    @9
    ssfi
    sylancr
    @6
    @9
    unfi
    syl2anc
    eqeltrd
end
