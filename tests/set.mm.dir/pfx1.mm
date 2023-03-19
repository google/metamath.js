include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cpfx.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "cfv.mm"
include "cs1.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "a1i.mm"
include "pfxval.mm"
include "sylan2.mm"
include "1e0p1.mm"
include "opeq2i.mm"
include "oveq2i.mm"
include "chash.mm"
include "cfzo.mm"
include "cn.mm"
include "lennncl.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "swrds1.mm"
include "syldan.mm"
include "3eqtrd.mm"

theorem pfx1
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( W prefix 1 ) = <" ( W ` 0 ) "> )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    cW
    c1
    cpfx
    co
    #
    cW
    cc0
    c1
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    cc0
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cc0
    cW
    cfv
    cs1
    #
    @2
    @1
    c1
    cn0
    wcel
    #
    @4
    @6
    wceq
    @11
    @2
    1nn0
    a1i
    cW
    c1
    @0
    pfxval
    sylan2
    @6
    @9
    wceq
    @3
    @5
    @8
    cW
    csubstr
    c1
    @7
    cc0
    1e0p1
    opeq2i
    oveq2i
    a1i
    @1
    @2
    cc0
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    @9
    @10
    wceq
    @3
    @12
    cn
    wcel
    @13
    cV
    cW
    lennncl
    @12
    lbfzo0
    sylibr
    cV
    cc0
    cW
    swrds1
    syldan
    3eqtrd
end
