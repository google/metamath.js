include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "simpr.mm"
include "simpl3.mm"
include "mulgnnp1.mm"
include "syl2anc.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "mndlid.mm"
include "mulg0.mm"
include "adantl.mm"
include "oveq1d.mm"
include "mulg1.mm"
include "3eqtr4rd.mm"
include "3adant2.mm"
include "oveq1.mm"
include "1e0p1.mm"
include "syl6eqr.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wo.mm"
include "simp2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem mulgnn0p1
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  assume mulgnn0p1.b: |- B = ( Base ` G )
  assume mulgnn0p1.t: |- .x. = ( .g ` G )
  assume mulgnn0p1.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ N e. NN0 /\ X e. B ) -> ( ( N + 1 ) .x. X ) = ( ( N .x. X ) .+ X ) )

  proof
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cN
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    wceq
    #
    cN
    cc0
    wceq
    #
    @3
    @4
    wa
    @4
    @2
    @9
    @3
    @4
    simpr
    @0
    @1
    @2
    @4
    simpl3
    cB
    c.pl
    c.x
    cG
    cN
    cX
    mulgnn0p1.b
    mulgnn0p1.t
    mulgnn0p1.p
    mulgnnp1
    syl2anc
    @3
    @10
    @9
    @3
    @9
    @10
    c1
    cX
    c.x
    co
    #
    cc0
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    wceq
    #
    @0
    @2
    @14
    @1
    @0
    @2
    wa
    #
    cG
    c0g
    cfv
    #
    cX
    c.pl
    co
    cX
    @13
    @11
    cB
    c.pl
    cG
    cX
    @16
    mulgnn0p1.b
    mulgnn0p1.p
    @16
    eqid
    #
    mndlid
    @15
    @12
    @16
    cX
    c.pl
    @2
    @12
    @16
    wceq
    @0
    cB
    c.x
    cG
    cX
    @16
    mulgnn0p1.b
    @17
    mulgnn0p1.t
    mulg0
    adantl
    oveq1d
    @2
    @11
    cX
    wceq
    @0
    cB
    c.x
    cG
    cX
    mulgnn0p1.b
    mulgnn0p1.t
    mulg1
    adantl
    3eqtr4rd
    3adant2
    @10
    @6
    @11
    @8
    @13
    @10
    @5
    c1
    cX
    c.x
    @10
    @5
    cc0
    c1
    caddc
    co
    c1
    cN
    cc0
    c1
    caddc
    oveq1
    1e0p1
    syl6eqr
    oveq1d
    @10
    @7
    @12
    cX
    c.pl
    cN
    cc0
    cX
    c.x
    oveq1
    oveq1d
    eqeq12d
    syl5ibrcom
    imp
    @3
    @1
    @4
    @10
    wo
    @0
    @1
    @2
    simp2
    cN
    elnn0
    sylib
    mpjaodan
end
