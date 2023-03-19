include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "wfn.mm"
include "cop.mm"
include "cfzo.mm"
include "co.mm"
include "wrdfn.mm"
include "adantr.mm"
include "oveq2.mm"
include "fzo0to3tp.mm"
include "syl6req.mm"
include "adantl.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "c0ex.mm"
include "1ex.mm"
include "2ex.mm"
include "fntpb.mm"
include "sylib.mm"

theorem wrd3tpop
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) = 3 ) -> W = { <. 0 , ( W ` 0 ) >. , <. 1 , ( W ` 1 ) >. , <. 2 , ( W ` 2 ) >. } )

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
    c3
    wceq
    #
    wa
    #
    cW
    cc0
    c1
    c2
    ctp
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
    c2
    c2
    cW
    cfv
    cop
    ctp
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
    c3
    cfzo
    co
    @4
    @1
    c3
    cc0
    cfzo
    oveq2
    fzo0to3tp
    syl6req
    adantl
    fneq2d
    mpbird
    cc0
    c1
    c2
    cW
    c0ex
    1ex
    2ex
    fntpb
    sylib
end
