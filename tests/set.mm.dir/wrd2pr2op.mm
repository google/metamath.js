include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wfn.mm"
include "cop.mm"
include "cfzo.mm"
include "co.mm"
include "wrdfn.mm"
include "adantr.mm"
include "oveq2.mm"
include "fzo0to2pr.mm"
include "syl6req.mm"
include "adantl.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "c0ex.mm"
include "1ex.mm"
include "fnprb.mm"
include "sylib.mm"

theorem wrd2pr2op
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) = 2 ) -> W = { <. 0 , ( W ` 0 ) >. , <. 1 , ( W ` 1 ) >. } )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cW
    cc0
    c1
    cpr
    #
    wfn
    #
    cW
    cc0
    cc0
    cW
    cfv
    cop
    c1
    c1
    cW
    cfv
    cop
    cpr
    wceq
    @3
    @5
    cW
    cc0
    @1
    cfzo
    co
    #
    wfn
    #
    @0
    @7
    @2
    cV
    cW
    wrdfn
    adantr
    @3
    @4
    @6
    cW
    @2
    @4
    @6
    wceq
    @0
    @2
    @6
    cc0
    c2
    cfzo
    co
    @4
    @1
    c2
    cc0
    cfzo
    oveq2
    fzo0to2pr
    syl6req
    adantl
    fneq2d
    mpbird
    cc0
    c1
    cW
    c0ex
    1ex
    fnprb
    sylib
end
