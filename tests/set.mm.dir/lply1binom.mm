include "ccrg.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ccmn.mm"
include "wceq.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "vr1cl.mm"
include "syl.mm"
include "simp3.mm"
include "cmncom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "cbs.mm"
include "cfv.mm"
include "ply1crng.mm"
include "simp2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "crngbinom.mm"
include "syl22anc.mm"
include "eqtrd.mm"

theorem lply1binom
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let cX: class X
  let cK: class K
  assume cply1binom.p: |- P = ( Poly1 ` R )
  assume cply1binom.x: |- X = ( var1 ` R )
  assume cply1binom.a: |- .+ = ( +g ` P )
  assume cply1binom.m: |- .X. = ( .r ` P )
  assume cply1binom.t: |- .x. = ( .g ` P )
  assume cply1binom.g: |- G = ( mulGrp ` P )
  assume cply1binom.e: |- .^ = ( .g ` G )
  assume cply1binom.b: |- B = ( Base ` P )

  disjoint A k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint X k
  disjoint .X. k
  disjoint .x. k
  disjoint .^ k
  disjoint .+ k
  disjoint K k
  assert |- ( ( R e. CRing /\ N e. NN0 /\ A e. B ) -> ( N .^ ( X .+ A ) ) = ( P gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( ( N - k ) .^ A ) .X. ( k .^ X ) ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cB
    wcel
    #
    w3a
    #
    cN
    cX
    cA
    c.pl
    co
    #
    c.ex
    co
    cN
    cA
    cX
    c.pl
    co
    #
    c.ex
    co
    #
    cP
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
    @7
    cmin
    co
    cA
    c.ex
    co
    @7
    cX
    c.ex
    co
    c.xp
    co
    c.x
    co
    cmpt
    cgsu
    co
    #
    @3
    @4
    @5
    cN
    c.ex
    @3
    cP
    ccmn
    wcel
    #
    cX
    cB
    wcel
    #
    @2
    @4
    @5
    wceq
    @0
    @1
    @9
    @2
    @0
    cR
    crg
    wcel
    #
    cP
    crg
    wcel
    @9
    cR
    crngring
    #
    cP
    cR
    cply1binom.p
    ply1ring
    cP
    ringcmn
    3syl
    3ad2ant1
    @0
    @1
    @10
    @2
    @0
    @11
    @10
    @12
    cB
    cP
    cR
    cX
    cply1binom.x
    cply1binom.p
    cply1binom.b
    vr1cl
    syl
    #
    3ad2ant1
    @0
    @1
    @2
    simp3
    cB
    c.pl
    cP
    cX
    cA
    cply1binom.b
    cply1binom.a
    cmncom
    syl3anc
    oveq2d
    @3
    cP
    ccrg
    wcel
    #
    @1
    cA
    cP
    cbs
    cfv
    #
    wcel
    #
    cX
    @15
    wcel
    #
    @6
    @8
    wceq
    @0
    @1
    @14
    @2
    cP
    cR
    cply1binom.p
    ply1crng
    3ad2ant1
    @0
    @1
    @2
    simp2
    @2
    @0
    @16
    @1
    @2
    @16
    cB
    @15
    cA
    cply1binom.b
    eleq2i
    biimpi
    3ad2ant3
    @0
    @1
    @17
    @2
    @0
    cX
    cB
    @15
    @13
    cply1binom.b
    syl6eleq
    3ad2ant1
    cA
    cX
    c.pl
    cP
    @15
    c.x
    c.xp
    vk
    c.ex
    cG
    cN
    @15
    eqid
    cply1binom.m
    cply1binom.t
    cply1binom.a
    cply1binom.g
    cply1binom.e
    crngbinom
    syl22anc
    eqtrd
end
