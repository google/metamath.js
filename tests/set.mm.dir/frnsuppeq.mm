include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "csupp.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wceq.mm"
include "cvv.mm"
include "wi.mm"
include "fex.mm"
include "expcom.mm"
include "adantr.mm"
include "imp.mm"
include "simplr.mm"
include "suppimacnv.mm"
include "syl2anc.mm"
include "cin.mm"
include "invdif.mm"
include "imaeq2i.mm"
include "wfun.mm"
include "ffun.mm"
include "inpreima.mm"
include "syl.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "fimacnv.mm"
include "eqtr4d.mm"
include "syl5sseq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtrd.mm"
include "syl5reqr.mm"
include "adantl.mm"
include "ex.mm"

theorem frnsuppeq
  let cS: class S
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cZ: class Z


  assert |- ( ( I e. V /\ Z e. W ) -> ( F : I --> S -> ( F supp Z ) = ( `' F " ( S \ { Z } ) ) ) )

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
    csupp
    co
    #
    cF
    ccnv
    #
    cS
    cZ
    csn
    #
    cdif
    #
    cima
    #
    wceq
    @2
    @3
    wa
    #
    @4
    @5
    cvv
    @6
    cdif
    #
    cima
    #
    @8
    @9
    cF
    cvv
    wcel
    #
    @1
    @4
    @11
    wceq
    @2
    @3
    @12
    @0
    @3
    @12
    wi
    @1
    @3
    @0
    @12
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
    suppimacnv
    syl2anc
    @3
    @11
    @8
    wceq
    @2
    @3
    @8
    @5
    cS
    @10
    cin
    #
    cima
    #
    @11
    @13
    @7
    @5
    cS
    @6
    invdif
    imaeq2i
    @3
    @14
    @5
    cS
    cima
    #
    @11
    cin
    #
    @11
    @3
    cF
    wfun
    @14
    @16
    wceq
    cI
    cS
    cF
    ffun
    cS
    @10
    cF
    inpreima
    syl
    @3
    @11
    @15
    wss
    @16
    @11
    wceq
    @3
    cF
    cdm
    #
    @11
    @15
    cF
    @10
    cnvimass
    @3
    @17
    cI
    @15
    cI
    cS
    cF
    fdm
    cI
    cS
    cF
    fimacnv
    eqtr4d
    syl5sseq
    @11
    @15
    sseqin2
    sylib
    eqtrd
    syl5reqr
    adantl
    eqtrd
    ex
end
