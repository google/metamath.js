include "ccrg.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "csrg.mm"
include "ccmn.mm"
include "w3a.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "crg.mm"
include "crngring.mm"
include "ringsrg.mm"
include "syl.mm"
include "adantr.mm"
include "crngmgp.mm"
include "simpr.mm"
include "3jca.mm"
include "csrgbinom.mm"
include "sylan.mm"

theorem crngbinom
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
  assume crngbinom.s: |- S = ( Base ` R )
  assume crngbinom.m: |- .X. = ( .r ` R )
  assume crngbinom.t: |- .x. = ( .g ` R )
  assume crngbinom.a: |- .+ = ( +g ` R )
  assume crngbinom.g: |- G = ( mulGrp ` R )
  assume crngbinom.e: |- .^ = ( .g ` G )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint R k
  disjoint S k
  disjoint .x. k
  disjoint .X. k
  disjoint .^ k
  disjoint .+ k
  assert |- ( ( ( R e. CRing /\ N e. NN0 ) /\ ( A e. S /\ B e. S ) ) -> ( N .^ ( A .+ B ) ) = ( R gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( ( N - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cR
    csrg
    wcel
    #
    cG
    ccmn
    wcel
    #
    @1
    w3a
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
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
    @5
    cmin
    co
    cA
    c.ex
    co
    @5
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
    @2
    @3
    @4
    @1
    @0
    @3
    @1
    @0
    cR
    crg
    wcel
    @3
    cR
    crngring
    cR
    ringsrg
    syl
    adantr
    @0
    @4
    @1
    cR
    cG
    crngbinom.g
    crngmgp
    adantr
    @0
    @1
    simpr
    3jca
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
    crngbinom.s
    crngbinom.m
    crngbinom.t
    crngbinom.a
    crngbinom.g
    crngbinom.e
    csrgbinom
    sylan
end
