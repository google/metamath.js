include "csr.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cstf.mm"
include "cfv.mm"
include "coppr.mm"
include "cghm.mm"
include "wceq.mm"
include "crh.mm"
include "eqid.mm"
include "srngrhm.mm"
include "rhmghm.mm"
include "syl.mm"
include "oppradd.mm"
include "ghmlin.mm"
include "syl3an1.mm"
include "crg.mm"
include "srngring.mm"
include "ringacl.mm"
include "stafval.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem srngadd
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.as: class .*
  let cX: class X
  let cY: class Y
  assume srngcl.i: |- .* = ( *r ` R )
  assume srngcl.b: |- B = ( Base ` R )
  assume srngadd.p: |- .+ = ( +g ` R )


  assert |- ( ( R e. *Ring /\ X e. B /\ Y e. B ) -> ( .* ` ( X .+ Y ) ) = ( ( .* ` X ) .+ ( .* ` Y ) ) )

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
    c.pl
    co
    #
    cR
    cstf
    cfv
    #
    cfv
    #
    cX
    @5
    cfv
    #
    cY
    @5
    cfv
    #
    c.pl
    co
    #
    @4
    c.as
    cfv
    #
    cX
    c.as
    cfv
    #
    cY
    c.as
    cfv
    #
    c.pl
    co
    @0
    @5
    cR
    cR
    coppr
    cfv
    #
    cghm
    co
    wcel
    #
    @1
    @2
    @6
    @9
    wceq
    @0
    @5
    cR
    @13
    crh
    co
    wcel
    @14
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
    cR
    @13
    @5
    rhmghm
    syl
    c.pl
    c.pl
    cR
    @13
    cX
    @5
    cY
    cB
    srngcl.b
    srngadd.p
    c.pl
    cR
    @13
    @15
    srngadd.p
    oppradd
    ghmlin
    syl3an1
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
    @17
    cR
    srngring
    cB
    c.pl
    cR
    cX
    cY
    srngcl.b
    srngadd.p
    ringacl
    syl3an1
    @4
    cB
    cR
    @5
    c.as
    srngcl.b
    srngcl.i
    @16
    stafval
    syl
    @3
    @7
    @11
    @8
    @12
    c.pl
    @1
    @0
    @7
    @11
    wceq
    @2
    cX
    cB
    cR
    @5
    c.as
    srngcl.b
    srngcl.i
    @16
    stafval
    3ad2ant2
    @2
    @0
    @8
    @12
    wceq
    @1
    cY
    cB
    cR
    @5
    c.as
    srngcl.b
    srngcl.i
    @16
    stafval
    3ad2ant3
    oveq12d
    3eqtr3d
end
