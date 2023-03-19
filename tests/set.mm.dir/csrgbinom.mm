include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "3simpb.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl2.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cmncom.mm"
include "syl3anc.mm"
include "srgbinom.mm"
include "syl13anc.mm"

theorem csrgbinom
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  assume srgbinom.s: |- S = ( Base ` R )
  assume srgbinom.m: |- .X. = ( .r ` R )
  assume srgbinom.t: |- .x. = ( .g ` R )
  assume srgbinom.a: |- .+ = ( +g ` R )
  assume srgbinom.g: |- G = ( mulGrp ` R )
  assume srgbinom.e: |- .^ = ( .g ` G )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint R k
  disjoint S k
  disjoint .x. k
  disjoint .^ k
  disjoint .X. k
  disjoint .+ k
  disjoint A n
  disjoint A x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint B n
  disjoint B x
  disjoint N n
  disjoint N x
  disjoint R n
  disjoint R x
  disjoint S n
  disjoint S x
  disjoint .x. n
  disjoint .x. x
  disjoint .^ n
  disjoint .^ x
  disjoint .X. n
  disjoint .X. x
  disjoint .+ n
  disjoint .+ x
  assert |- ( ( ( R e. SRing /\ G e. CMnd /\ N e. NN0 ) /\ ( A e. S /\ B e. S ) ) -> ( N .^ ( A .+ B ) ) = ( R gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( ( N - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  proof
    cR
    csrg
    wcel
    #
    cG
    ccmn
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    wa
    #
    @0
    @2
    wa
    #
    @4
    @5
    cA
    cB
    c.xp
    co
    cB
    cA
    c.xp
    co
    wceq
    #
    cN
    cA
    cB
    c.pl
    co
    c.ex
    co
    cR
    vk
    cc0
    cN
    cfz
    co
    cN
    vk
    cv
    #
    cbc
    co
    cN
    @10
    cmin
    co
    cA
    c.ex
    co
    @10
    cB
    c.ex
    co
    c.xp
    co
    c.x
    co
    cmpt
    cgsu
    co
    wceq
    @3
    @8
    @6
    @0
    @1
    @2
    3simpb
    adantr
    @3
    @4
    @5
    simprl
    #
    @3
    @4
    @5
    simprr
    #
    @7
    @1
    @4
    @5
    @9
    @0
    @1
    @2
    @6
    simpl2
    @11
    @12
    cS
    c.xp
    cG
    cA
    cB
    cS
    cR
    cG
    srgbinom.g
    srgbinom.s
    mgpbas
    cR
    c.xp
    cG
    srgbinom.g
    srgbinom.m
    mgpplusg
    cmncom
    syl3anc
    cA
    cB
    c.pl
    cR
    cS
    c.x
    c.xp
    vk
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinom
    syl13anc
end
