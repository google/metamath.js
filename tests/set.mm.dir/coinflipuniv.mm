include "cdm.mm"
include "cuni.mm"
include "cpr.mm"
include "cpw.mm"
include "coinflipspace.mm"
include "unieqi.mm"
include "unipw.mm"
include "eqtri.mm"

theorem coinflipuniv
  let cP: class P
  let cT: class T
  let cH: class H
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume coinflip.h: |- H e. _V
  assume coinflip.t: |- T e. _V
  assume coinflip.th: |- H =/= T
  assume coinflip.2: |- P = ( ( # |` ~P { H , T } ) oFC / 2 )
  assume coinflip.3: |- X = { <. H , 1 >. , <. T , 0 >. }


  assert |- U. dom P = { H , T }

  proof
    cP
    cdm
    #
    cuni
    cH
    cT
    cpr
    #
    cpw
    #
    cuni
    @1
    @0
    @2
    cP
    cT
    cH
    cX
    coinflip.h
    coinflip.t
    coinflip.th
    coinflip.2
    coinflip.3
    coinflipspace
    unieqi
    @1
    unipw
    eqtri
end
