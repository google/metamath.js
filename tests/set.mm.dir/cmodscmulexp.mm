include "cclm.mm"
include "wcel.mm"
include "ci.mm"
include "cn.mm"
include "w3a.mm"
include "wa.mm"
include "clmod.mm"
include "cexp.mm"
include "co.mm"
include "clmlmod.mm"
include "adantr.mm"
include "simp1.mm"
include "anim2i.mm"
include "simpr3.mm"
include "cmodscexp.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "lmodvscl.mm"
include "syl3anc.mm"

theorem cmodscmulexp
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  assume cmodscexp.f: |- F = ( Scalar ` W )
  assume cmodscexp.k: |- K = ( Base ` F )
  assume cmodscmulexp.x: |- X = ( Base ` W )
  assume cmodscmulexp.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CMod /\ ( _i e. K /\ B e. X /\ N e. NN ) ) -> ( ( _i ^ N ) .x. B ) e. X )

  proof
    cW
    cclm
    wcel
    #
    ci
    cK
    wcel
    #
    cB
    cX
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    wa
    #
    cW
    clmod
    wcel
    #
    ci
    cN
    cexp
    co
    #
    cK
    wcel
    #
    @2
    @7
    cB
    c.x
    co
    cX
    wcel
    @0
    @6
    @4
    cW
    clmlmod
    adantr
    @5
    @0
    @1
    wa
    @3
    @8
    @4
    @1
    @0
    @1
    @2
    @3
    simp1
    anim2i
    @0
    @1
    @2
    @3
    simpr3
    cF
    cK
    cN
    cW
    cmodscexp.f
    cmodscexp.k
    cmodscexp
    syl2anc
    @0
    @1
    @2
    @3
    simpr2
    @7
    c.x
    cF
    cK
    cX
    cW
    cB
    cmodscmulexp.x
    cmodscexp.f
    cmodscmulexp.s
    cmodscexp.k
    lmodvscl
    syl3anc
end
