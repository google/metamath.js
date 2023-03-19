include "wcel.mm"
include "c2.mm"
include "crelexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "ccom.mm"
include "wceq.mm"
include "df-2.mm"
include "oveq2i.mm"
include "a1i.mm"
include "cn.mm"
include "1nn.mm"
include "relexpsucnnr.mm"
include "mpan2.mm"
include "relexp1g.mm"
include "coeq1d.mm"
include "3eqtrd.mm"

theorem relexp2
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R ^r 2 ) = ( R o. R ) )

  proof
    cR
    cV
    wcel
    #
    cR
    c2
    crelexp
    co
    #
    cR
    c1
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    c1
    crelexp
    co
    #
    cR
    ccom
    #
    cR
    cR
    ccom
    @1
    @3
    wceq
    @0
    c2
    @2
    cR
    crelexp
    df-2
    oveq2i
    a1i
    @0
    c1
    cn
    wcel
    @3
    @5
    wceq
    1nn
    cR
    c1
    cV
    relexpsucnnr
    mpan2
    @0
    @4
    cR
    cR
    cR
    cV
    relexp1g
    coeq1d
    3eqtrd
end
