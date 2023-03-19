include "csr.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cstf.mm"
include "cfv.mm"
include "coppr.mm"
include "cmulr.mm"
include "crh.mm"
include "wceq.mm"
include "eqid.mm"
include "srngrhm.mm"
include "rhmmul.mm"
include "syl3an1.mm"
include "opprmul.mm"
include "syl6eq.mm"
include "crg.mm"
include "srngring.mm"
include "ringcl.mm"
include "stafval.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem srngmul
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.as: class .*
  let cX: class X
  let cY: class Y
  assume srngcl.i: |- .* = ( *r ` R )
  assume srngcl.b: |- B = ( Base ` R )
  assume srngmul.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. *Ring /\ X e. B /\ Y e. B ) -> ( .* ` ( X .x. Y ) ) = ( ( .* ` Y ) .x. ( .* ` X ) ) )

  proof
    cR
    csr
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
    w3a
    #
    cX
    cY
    c.x
    co
    #
    cR
    cstf
    cfv
    #
    cfv
    #
    cY
    @5
    cfv
    #
    cX
    @5
    cfv
    #
    c.x
    co
    #
    @4
    c.as
    cfv
    #
    cY
    c.as
    cfv
    #
    cX
    c.as
    cfv
    #
    c.x
    co
    @3
    @6
    @8
    @7
    cR
    coppr
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    @9
    @0
    @5
    cR
    @13
    crh
    co
    wcel
    @1
    @2
    @6
    @15
    wceq
    cR
    @5
    @13
    @13
    eqid
    #
    @5
    eqid
    #
    srngrhm
    cX
    cY
    cR
    @13
    c.x
    @14
    @5
    cB
    srngcl.b
    srngmul.t
    @14
    eqid
    #
    rhmmul
    syl3an1
    cB
    cR
    @14
    c.x
    @13
    @8
    @7
    srngcl.b
    srngmul.t
    @16
    @18
    opprmul
    syl6eq
    @3
    @4
    cB
    wcel
    #
    @6
    @10
    wceq
    @0
    cR
    crg
    wcel
    @1
    @2
    @19
    cR
    srngring
    cB
    cR
    c.x
    cX
    cY
    srngcl.b
    srngmul.t
    ringcl
    syl3an1
    @4
    cB
    cR
    @5
    c.as
    srngcl.b
    srngcl.i
    @17
    stafval
    syl
    @3
    @7
    @11
    @8
    @12
    c.x
    @2
    @0
    @7
    @11
    wceq
    @1
    cY
    cB
    cR
    @5
    c.as
    srngcl.b
    srngcl.i
    @17
    stafval
    3ad2ant3
    @1
    @0
    @8
    @12
    wceq
    @2
    cX
    cB
    cR
    @5
    c.as
    srngcl.b
    srngcl.i
    @17
    stafval
    3ad2ant2
    oveq12d
    3eqtr3d
end
