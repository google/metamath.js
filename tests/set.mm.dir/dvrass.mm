include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringcl.mm"
include "3adant3r3.mm"
include "dvrval.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem dvrass
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvrass.b: |- B = ( Base ` R )
  assume dvrass.o: |- U = ( Unit ` R )
  assume dvrass.d: |- ./ = ( /r ` R )
  assume dvrass.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. B /\ Z e. U ) ) -> ( ( X .x. Y ) ./ Z ) = ( X .x. ( Y ./ Z ) ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cU
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cY
    c.x
    co
    #
    cZ
    cR
    cinvr
    cfv
    #
    cfv
    #
    c.x
    co
    #
    cX
    cY
    @8
    c.x
    co
    #
    c.x
    co
    #
    @6
    cZ
    c.dv
    co
    #
    cX
    cY
    cZ
    c.dv
    co
    #
    c.x
    co
    @5
    @0
    @1
    @2
    @8
    cB
    wcel
    #
    @9
    @11
    wceq
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    #
    @5
    @0
    @3
    @14
    @15
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    cR
    cU
    @7
    cZ
    dvrass.o
    @7
    eqid
    #
    dvrass.b
    ringinvcl
    syl2anc
    cB
    cR
    c.x
    cX
    cY
    @8
    dvrass.b
    dvrass.t
    ringass
    syl13anc
    @5
    @6
    cB
    wcel
    #
    @3
    @12
    @9
    wceq
    @0
    @1
    @2
    @19
    @3
    cB
    cR
    c.x
    cX
    cY
    dvrass.b
    dvrass.t
    ringcl
    3adant3r3
    @17
    cB
    c.dv
    cR
    c.x
    cU
    @7
    @6
    cZ
    dvrass.b
    dvrass.t
    dvrass.o
    @18
    dvrass.d
    dvrval
    syl2anc
    @5
    @13
    @10
    cX
    c.x
    @5
    @2
    @3
    @13
    @10
    wceq
    @16
    @17
    cB
    c.dv
    cR
    c.x
    cU
    @7
    cY
    cZ
    dvrass.b
    dvrass.t
    dvrass.o
    @18
    dvrass.d
    dvrval
    syl2anc
    oveq2d
    3eqtr4d
end
