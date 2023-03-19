include "c0.mm"
include "rel0.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "noel.mm"
include "pm2.21i.mm"
include "sylbi.mm"
include "adantr.mm"
include "2false.mm"
include "bitr4i.mm"
include "iseri.mm"

theorem 0er
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- (/) Er (/)

  proof
    vx
    vy
    vz
    c0
    c0
    rel0
    vx
    cv
    #
    vy
    cv
    #
    c0
    wbr
    #
    @0
    @1
    cop
    #
    c0
    wcel
    #
    @1
    @0
    c0
    wbr
    #
    @0
    @1
    c0
    df-br
    #
    @4
    @5
    @3
    noel
    #
    pm2.21i
    sylbi
    @2
    @0
    vz
    cv
    #
    c0
    wbr
    #
    @1
    @8
    c0
    wbr
    @2
    @4
    @9
    @6
    @4
    @9
    @7
    pm2.21i
    sylbi
    adantr
    @0
    c0
    wcel
    #
    @0
    @0
    cop
    #
    c0
    wcel
    #
    @0
    @0
    c0
    wbr
    @10
    @12
    @0
    noel
    @11
    noel
    2false
    @0
    @0
    c0
    df-br
    bitr4i
    iseri
end
