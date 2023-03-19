include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wo.mm"
include "wn.mm"
include "zeo3.mm"
include "oddp1even.mm"
include "bicomd.mm"
include "orbi2d.mm"
include "mpbird.mm"

theorem zeo5
  let cN: class N


  assert |- ( N e. ZZ -> ( 2 || N \/ 2 || ( N + 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    c2
    cN
    c1
    caddc
    co
    cdvds
    wbr
    #
    wo
    @1
    @1
    wn
    #
    wo
    cN
    zeo3
    @0
    @2
    @3
    @1
    @0
    @3
    @2
    cN
    oddp1even
    bicomd
    orbi2d
    mpbird
end
