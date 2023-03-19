include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wceq.mm"
include "wf.mm"
include "fex.mm"
include "syl2anc.mm"
include "suppimacnv.mm"
include "fisuppfi.mm"
include "eqeltrd.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "syl.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem fidmfisupp
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  let cZ: class Z
  assume fidmfisupp.1: |- ( ph -> F : D --> R )
  assume fidmfisupp.2: |- ( ph -> D e. Fin )
  assume fidmfisupp.3: |- ( ph -> Z e. V )


  assert |- ( ph -> F finSupp Z )

  proof
    wph
    cF
    cZ
    cfsupp
    wbr
    #
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    @1
    cF
    ccnv
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cfn
    wph
    cF
    cvv
    wcel
    #
    cZ
    cV
    wcel
    #
    @1
    @4
    wceq
    wph
    cD
    cR
    cF
    wf
    #
    cD
    cfn
    wcel
    @5
    fidmfisupp.1
    fidmfisupp.2
    cD
    cR
    cfn
    cF
    fex
    syl2anc
    #
    fidmfisupp.3
    cF
    cvv
    cV
    cZ
    suppimacnv
    syl2anc
    wph
    cD
    cR
    @3
    cF
    fidmfisupp.2
    fidmfisupp.1
    fisuppfi
    eqeltrd
    wph
    cF
    wfun
    #
    @5
    @6
    @0
    @2
    wb
    wph
    @7
    @9
    fidmfisupp.1
    cD
    cR
    cF
    ffun
    syl
    @8
    fidmfisupp.3
    cF
    cvv
    cV
    cZ
    funisfsupp
    syl3anc
    mpbird
end
