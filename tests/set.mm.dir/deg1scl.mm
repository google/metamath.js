include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "deg1sclle.mm"
include "3adant3.mm"
include "cn0.mm"
include "wb.mm"
include "cbs.mm"
include "c0g.mm"
include "simp1.mm"
include "eqid.mm"
include "ply1sclcl.mm"
include "ply1scln0.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "nn0le0eq0.mm"
include "syl.mm"
include "mpbid.mm"

theorem deg1scl
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  let c.0: class .0.
  assume deg1sclle.d: |- D = ( deg1 ` R )
  assume deg1sclle.p: |- P = ( Poly1 ` R )
  assume deg1sclle.k: |- K = ( Base ` R )
  assume deg1sclle.a: |- A = ( algSc ` P )
  assume deg1scl.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ F e. K /\ F =/= .0. ) -> ( D ` ( A ` F ) ) = 0 )

  proof
    cR
    crg
    wcel
    #
    cF
    cK
    wcel
    #
    cF
    c.0
    wne
    #
    w3a
    #
    cF
    cA
    cfv
    #
    cD
    cfv
    #
    cc0
    cle
    wbr
    #
    @5
    cc0
    wceq
    #
    @0
    @1
    @6
    @2
    cA
    cD
    cP
    cR
    cF
    cK
    deg1sclle.d
    deg1sclle.p
    deg1sclle.k
    deg1sclle.a
    deg1sclle
    3adant3
    @3
    @5
    cn0
    wcel
    #
    @6
    @7
    wb
    @3
    @0
    @4
    cP
    cbs
    cfv
    #
    wcel
    #
    @4
    cP
    c0g
    cfv
    #
    wne
    @8
    @0
    @1
    @2
    simp1
    @0
    @1
    @10
    @2
    cA
    @9
    cP
    cR
    cF
    cK
    deg1sclle.p
    deg1sclle.a
    deg1sclle.k
    @9
    eqid
    #
    ply1sclcl
    3adant3
    cA
    cP
    cR
    cK
    cF
    @11
    c.0
    deg1sclle.p
    deg1sclle.a
    deg1scl.z
    @11
    eqid
    #
    deg1sclle.k
    ply1scln0
    @9
    cD
    cP
    cR
    @4
    @11
    deg1sclle.d
    deg1sclle.p
    @13
    @12
    deg1nn0cl
    syl3anc
    @5
    nn0le0eq0
    syl
    mpbid
end
