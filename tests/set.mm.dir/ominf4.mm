include "com.mm"
include "cfin4.mm"
include "wcel.mm"
include "id.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "peano1.mm"
include "difsnpss.mm"
include "mpbi.mm"
include "limom.mm"
include "limenpsi.mm"
include "ensymd.mm"
include "fin4i.mm"
include "sylancr.mm"
include "pm2.65i.mm"

theorem ominf4
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- -. _om e. Fin4

  proof
    com
    cfin4
    wcel
    #
    @0
    @0
    id
    @0
    com
    c0
    csn
    cdif
    #
    com
    wpss
    #
    @1
    com
    cen
    wbr
    @0
    wn
    c0
    com
    wcel
    @2
    peano1
    c0
    com
    difsnpss
    mpbi
    @0
    com
    @1
    com
    cfin4
    limom
    limenpsi
    ensymd
    com
    @1
    fin4i
    sylancr
    pm2.65i
end
