include "wcel.mm"
include "c2.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq1i.mm"
include "cn.mm"
include "wceq.mm"
include "1nn.mm"
include "mulgnnp1.mm"
include "mpan.mm"
include "syl5eq.mm"
include "mulg1.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem mulg2
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cX: class X
  assume mulg1.b: |- B = ( Base ` G )
  assume mulg1.m: |- .x. = ( .g ` G )
  assume mulgnnp1.p: |- .+ = ( +g ` G )


  assert |- ( X e. B -> ( 2 .x. X ) = ( X .+ X ) )

  proof
    cX
    cB
    wcel
    #
    c2
    cX
    c.x
    co
    #
    c1
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    #
    cX
    cX
    c.pl
    co
    @0
    @1
    c1
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    @3
    c2
    @4
    cX
    c.x
    df-2
    oveq1i
    c1
    cn
    wcel
    @0
    @5
    @3
    wceq
    1nn
    cB
    c.pl
    c.x
    cG
    c1
    cX
    mulg1.b
    mulg1.m
    mulgnnp1.p
    mulgnnp1
    mpan
    syl5eq
    @0
    @2
    cX
    cX
    c.pl
    cB
    c.x
    cG
    cX
    mulg1.b
    mulg1.m
    mulg1
    oveq1d
    eqtrd
end
