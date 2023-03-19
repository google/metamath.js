include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "ccnv.mm"
include "wfun.mm"
include "eqid.mm"
include "wlkf.mm"
include "wa.mm"
include "cv.mm"
include "cs1.mm"
include "wrex.mm"
include "wrdl1exs1.mm"
include "funcnvs1.mm"
include "cnveq.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "syl.mm"
include "sylan.mm"

theorem uhgrwkspthlem1
  let cP: class P
  let cF: class F
  let cG: class G
  let vi: setvar i


  assert |- ( ( F ( Walks ` G ) P /\ ( # ` F ) = 1 ) -> Fun `' F )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cF
    chash
    cfv
    c1
    wceq
    #
    cF
    ccnv
    #
    wfun
    #
    cP
    cF
    cG
    @0
    @0
    eqid
    wlkf
    @2
    @3
    wa
    cF
    vi
    cv
    #
    cs1
    #
    wceq
    #
    vi
    @1
    wrex
    @5
    @1
    cF
    vi
    wrdl1exs1
    @8
    @5
    vi
    @1
    @8
    @5
    @7
    ccnv
    #
    wfun
    @6
    funcnvs1
    @8
    @4
    @9
    cF
    @7
    cnveq
    funeqd
    mpbiri
    rexlimivw
    syl
    sylan
end
