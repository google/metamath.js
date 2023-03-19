include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wor.mm"
include "sonr.mm"
include "mpan.mm"
include "adantl.mm"
include "brel.mm"
include "con3i.mm"
include "pm2.61i.mm"

theorem soirri
  let cA: class A
  let cR: class R
  let cS: class S
  assume soi.1: |- R Or S
  assume soi.2: |- R C_ ( S X. S )


  assert |- -. A R A

  proof
    cA
    cS
    wcel
    #
    @0
    wa
    #
    cA
    cA
    cR
    wbr
    #
    wn
    #
    @0
    @3
    @0
    cS
    cR
    wor
    @0
    @3
    soi.1
    cS
    cA
    cR
    sonr
    mpan
    adantl
    @2
    @1
    cA
    cA
    cS
    cS
    cR
    soi.2
    brel
    con3i
    pm2.61i
end
