include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "cfzo.mm"
include "wceq.mm"
include "s1cl.mm"
include "adantr.mm"
include "adantl.mm"
include "cn.mm"
include "c1.mm"
include "s1len.mm"
include "a1i.mm"
include "1nn.mm"
include "syl6eqel.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "s1fv.mm"
include "eqtrd.mm"

theorem ccat2s1p1
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. V /\ Y e. V ) -> ( ( <" X "> ++ <" Y "> ) ` 0 ) = X )

  proof
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cc0
    cX
    cs1
    #
    cY
    cs1
    #
    cconcat
    co
    cfv
    #
    cc0
    @3
    cfv
    #
    cX
    @2
    @3
    cV
    cword
    #
    wcel
    #
    @4
    @7
    wcel
    #
    cc0
    cc0
    @3
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    @5
    @6
    wceq
    @0
    @8
    @1
    cX
    cV
    s1cl
    adantr
    @1
    @9
    @0
    cY
    cV
    s1cl
    adantl
    @0
    @11
    @1
    @0
    @10
    cn
    wcel
    @11
    @0
    @10
    c1
    cn
    @10
    c1
    wceq
    @0
    cX
    s1len
    a1i
    1nn
    syl6eqel
    @10
    lbfzo0
    sylibr
    adantr
    cV
    @3
    @4
    cc0
    ccatval1
    syl3anc
    @0
    @6
    cX
    wceq
    @1
    cX
    cV
    s1fv
    adantr
    eqtrd
end
