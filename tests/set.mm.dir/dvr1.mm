include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "cui.mm"
include "wceq.mm"
include "id.mm"
include "eqid.mm"
include "1unit.mm"
include "dvrval.mm"
include "syl2anr.mm"
include "1rinv.mm"
include "adantr.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "3eqtrd.mm"

theorem dvr1
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let c.1: class .1.
  let cX: class X
  assume dvr1.b: |- B = ( Base ` R )
  assume dvr1.d: |- ./ = ( /r ` R )
  assume dvr1.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> ( X ./ .1. ) = X )

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
    cX
    c.1
    c.dv
    co
    #
    cX
    c.1
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    c.1
    @6
    co
    cX
    @1
    @1
    c.1
    cR
    cui
    cfv
    #
    wcel
    @3
    @7
    wceq
    @0
    @1
    id
    cR
    @8
    c.1
    @8
    eqid
    #
    dvr1.o
    1unit
    cB
    c.dv
    cR
    @6
    @8
    @4
    cX
    c.1
    dvr1.b
    @6
    eqid
    #
    @9
    @4
    eqid
    #
    dvr1.d
    dvrval
    syl2anr
    @2
    @5
    c.1
    cX
    @6
    @0
    @5
    c.1
    wceq
    @1
    cR
    c.1
    @4
    @11
    dvr1.o
    1rinv
    adantr
    oveq2d
    cB
    cR
    @6
    c.1
    cX
    dvr1.b
    @10
    dvr1.o
    ringridm
    3eqtrd
end
