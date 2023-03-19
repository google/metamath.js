include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "pw2eng.mm"
include "ax-mp.mm"

theorem pw2en
  let cA: class A
  let vx: setvar x
  let vz: setvar z
  let cV: class V
  assume pw2en.1: |- A e. _V


  assert |- ~P A ~~ ( 2o ^m A )

  proof
    cA
    cvv
    wcel
    cA
    cpw
    c2o
    cA
    cmap
    co
    cen
    wbr
    pw2en.1
    cA
    cvv
    pw2eng
    ax-mp
end
