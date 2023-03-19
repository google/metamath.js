include "ccnfld.mm"
include "ccrg.mm"
include "wcel.mm"
include "cabl.mm"
include "cncrng.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "unitabl.mm"
include "ax-mp.mm"

theorem cnmgpabl
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cnmgpabl.m: |- M = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )


  assert |- M e. Abel

  proof
    ccnfld
    ccrg
    wcel
    cM
    cabl
    wcel
    cncrng
    ccnfld
    cc
    cc0
    csn
    cdif
    cM
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    cnmgpabl.m
    unitabl
    ax-mp
end
