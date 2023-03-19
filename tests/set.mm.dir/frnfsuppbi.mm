include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cfn.mm"
include "wb.mm"
include "csupp.mm"
include "co.mm"
include "wfun.mm"
include "cvv.mm"
include "ffun.mm"
include "adantl.mm"
include "wi.mm"
include "fex.mm"
include "expcom.mm"
include "adantr.mm"
include "imp.mm"
include "simplr.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "wceq.mm"
include "frnsuppeq.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "ex.mm"

theorem frnfsuppbi
  let cS: class S
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cZ: class Z


  assert |- ( ( I e. V /\ Z e. W ) -> ( F : I --> S -> ( F finSupp Z <-> ( `' F " ( S \ { Z } ) ) e. Fin ) ) )

  proof
    cI
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    wa
    #
    cI
    cS
    cF
    wf
    #
    cF
    cZ
    cfsupp
    wbr
    #
    cF
    ccnv
    cS
    cZ
    csn
    cdif
    cima
    #
    cfn
    wcel
    #
    wb
    @2
    @3
    wa
    #
    @4
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    @6
    @7
    cF
    wfun
    #
    cF
    cvv
    wcel
    #
    @1
    @4
    @9
    wb
    @3
    @10
    @2
    cI
    cS
    cF
    ffun
    adantl
    @2
    @3
    @11
    @0
    @3
    @11
    wi
    @1
    @3
    @0
    @11
    cI
    cS
    cV
    cF
    fex
    expcom
    adantr
    imp
    @0
    @1
    @3
    simplr
    cF
    cvv
    cW
    cZ
    funisfsupp
    syl3anc
    @7
    @8
    @5
    cfn
    @2
    @3
    @8
    @5
    wceq
    cS
    cF
    cI
    cV
    cW
    cZ
    frnsuppeq
    imp
    eleq1d
    bitrd
    ex
end
