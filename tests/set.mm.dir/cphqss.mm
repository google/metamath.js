include "ccph.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "cq.mm"
include "wss.mm"
include "cphsubrg.mm"
include "cphsca.mm"
include "clvec.mm"
include "cphlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "qsssubdrg.mm"
include "syl2anc.mm"

theorem cphqss
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( W e. CPreHil -> QQ C_ K )

  proof
    cW
    ccph
    wcel
    #
    cK
    ccnfld
    csubrg
    cfv
    wcel
    ccnfld
    cK
    cress
    co
    #
    cdr
    wcel
    cq
    cK
    wss
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsubrg
    @0
    cF
    @1
    cdr
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsca
    @0
    cW
    clvec
    wcel
    cF
    cdr
    wcel
    cW
    cphlvec
    cF
    cW
    cphsca.f
    lvecdrng
    syl
    eqeltrrd
    cK
    qsssubdrg
    syl2anc
end
