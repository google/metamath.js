include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "wo.mm"
include "cn.mm"
include "wb.mm"
include "2nn.mm"
include "dvdsprime.mm"
include "mpan2.mm"
include "eqcom.mm"
include "biimpi.mm"
include "wne.mm"
include "wi.mm"
include "1ne2.mm"
include "necom.mm"
include "eqneqall.mm"
include "com12.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "jaoi.mm"
include "syl6bi.mm"
include "con3d.mm"
include "orrd.mm"

theorem prm2orodd
  let cP: class P


  assert |- ( P e. Prime -> ( P = 2 \/ -. 2 || P ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c2
    wceq
    #
    c2
    cP
    cdvds
    wbr
    #
    wn
    @0
    @2
    @1
    @0
    @2
    c2
    cP
    wceq
    #
    c2
    c1
    wceq
    #
    wo
    #
    @1
    @0
    c2
    cn
    wcel
    @2
    @5
    wb
    2nn
    cP
    c2
    dvdsprime
    mpan2
    @3
    @1
    @4
    @3
    @1
    c2
    cP
    eqcom
    biimpi
    c1
    c2
    wne
    #
    @4
    @1
    wi
    #
    1ne2
    @6
    c2
    c1
    wne
    #
    @7
    c1
    c2
    necom
    @4
    @8
    @1
    @1
    c2
    c1
    eqneqall
    com12
    sylbi
    ax-mp
    jaoi
    syl6bi
    con3d
    orrd
end
