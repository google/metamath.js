include "c0.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "rel0.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "noel.mm"
include "pm2.21i.mm"
include "sylbi.mm"
include "adantl.mm"
include "ad2antrl.mm"
include "wb.mm"
include "2false.mm"
include "bitr4i.mm"
include "iserd.mm"
include "trud.mm"

theorem 0erOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- (/) Er (/)

  proof
    c0
    c0
    wer
    wtru
    vx
    vy
    vz
    c0
    c0
    c0
    wrel
    wtru
    rel0
    a1i
    vx
    cv
    #
    vy
    cv
    #
    c0
    wbr
    #
    @1
    @0
    c0
    wbr
    #
    wtru
    @2
    @0
    @1
    cop
    #
    c0
    wcel
    #
    @3
    @0
    @1
    c0
    df-br
    #
    @5
    @3
    @4
    noel
    #
    pm2.21i
    sylbi
    adantl
    @2
    @0
    vz
    cv
    #
    c0
    wbr
    #
    wtru
    @1
    @8
    c0
    wbr
    @2
    @5
    @9
    @6
    @5
    @9
    @7
    pm2.21i
    sylbi
    ad2antrl
    @0
    c0
    wcel
    #
    @0
    @0
    c0
    wbr
    #
    wb
    wtru
    @10
    @0
    @0
    cop
    #
    c0
    wcel
    #
    @11
    @10
    @13
    @0
    noel
    @12
    noel
    2false
    @0
    @0
    c0
    df-br
    bitr4i
    a1i
    iserd
    trud
end
