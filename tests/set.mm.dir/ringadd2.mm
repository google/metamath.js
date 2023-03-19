include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "ringid.mm"
include "oveq12.mm"
include "anidms.mm"
include "eqcomd.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "eqeq2d.mm"
include "syl5ibr.mm"
include "adantrd.mm"
include "reximdva.mm"
include "mpd.mm"

theorem ringadd2
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cX: class X
  assume ringadd2.b: |- B = ( Base ` R )
  assume ringadd2.p: |- .+ = ( +g ` R )
  assume ringadd2.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint R x
  disjoint X x
  disjoint .x. x
  assert |- ( ( R e. Ring /\ X e. B ) -> E. x e. B ( X .+ X ) = ( ( x .+ x ) .x. X ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vx
    cv
    #
    cX
    c.x
    co
    #
    cX
    wceq
    #
    cX
    @3
    c.x
    co
    cX
    wceq
    #
    wa
    #
    vx
    cB
    wrex
    cX
    cX
    c.pl
    co
    #
    @3
    @3
    c.pl
    co
    cX
    c.x
    co
    #
    wceq
    #
    vx
    cB
    wrex
    vx
    cB
    cR
    c.x
    cX
    ringadd2.b
    ringadd2.t
    ringid
    @2
    @7
    @10
    vx
    cB
    @2
    @3
    cB
    wcel
    #
    wa
    #
    @5
    @10
    @6
    @5
    @10
    @12
    @8
    @4
    @4
    c.pl
    co
    #
    wceq
    @5
    @13
    @8
    @5
    @13
    @8
    wceq
    @4
    cX
    @4
    cX
    c.pl
    oveq12
    anidms
    eqcomd
    @12
    @9
    @13
    @8
    @12
    @0
    @11
    @11
    @1
    @9
    @13
    wceq
    @0
    @1
    @11
    simpll
    @2
    @11
    simpr
    #
    @14
    @0
    @1
    @11
    simplr
    cB
    c.pl
    cR
    c.x
    @3
    @3
    cX
    ringadd2.b
    ringadd2.p
    ringadd2.t
    ringdir
    syl13anc
    eqeq2d
    syl5ibr
    adantrd
    reximdva
    mpd
end
