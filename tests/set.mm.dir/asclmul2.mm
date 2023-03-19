include "casa.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cur.mm"
include "wceq.mm"
include "eqid.mm"
include "asclval.mm"
include "3ad2ant2.mm"
include "oveq2d.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "crg.mm"
include "assaring.mm"
include "3ad2ant1.mm"
include "ringidcl.mm"
include "syl.mm"
include "assaassr.mm"
include "syl13anc.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem asclmul2
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume asclmul1.a: |- A = ( algSc ` W )
  assume asclmul1.f: |- F = ( Scalar ` W )
  assume asclmul1.k: |- K = ( Base ` F )
  assume asclmul1.v: |- V = ( Base ` W )
  assume asclmul1.t: |- .X. = ( .r ` W )
  assume asclmul1.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. AssAlg /\ R e. K /\ X e. V ) -> ( X .X. ( A ` R ) ) = ( R .x. X ) )

  proof
    cW
    casa
    wcel
    #
    cR
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cX
    cR
    cA
    cfv
    #
    c.xp
    co
    cX
    cR
    cW
    cur
    cfv
    #
    c.x
    co
    #
    c.xp
    co
    #
    cR
    cX
    @5
    c.xp
    co
    #
    c.x
    co
    #
    cR
    cX
    c.x
    co
    @3
    @4
    @6
    cX
    c.xp
    @1
    @0
    @4
    @6
    wceq
    @2
    cA
    c.x
    @5
    cF
    cK
    cW
    cR
    asclmul1.a
    asclmul1.f
    asclmul1.k
    asclmul1.s
    @5
    eqid
    #
    asclval
    3ad2ant2
    oveq2d
    @3
    @0
    @1
    @2
    @5
    cV
    wcel
    #
    @7
    @9
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @3
    cW
    crg
    wcel
    #
    @11
    @0
    @1
    @13
    @2
    cW
    assaring
    3ad2ant1
    #
    cV
    cW
    @5
    asclmul1.v
    @10
    ringidcl
    syl
    cR
    cK
    c.x
    c.xp
    cF
    cV
    cW
    cX
    @5
    asclmul1.v
    asclmul1.f
    asclmul1.k
    asclmul1.s
    asclmul1.t
    assaassr
    syl13anc
    @3
    @8
    cX
    cR
    c.x
    @3
    @13
    @2
    @8
    cX
    wceq
    @14
    @12
    cV
    cW
    c.xp
    @5
    cX
    asclmul1.v
    asclmul1.t
    @10
    ringridm
    syl2anc
    oveq2d
    3eqtrd
end
