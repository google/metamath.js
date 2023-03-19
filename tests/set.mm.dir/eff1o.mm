include "cpi.mm"
include "cneg.mm"
include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ce.mm"
include "cres.mm"
include "wf1o.mm"
include "pire.mm"
include "renegcli.mm"
include "cioc.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "cfv.mm"
include "cmpt.mm"
include "eqid.mm"
include "cxr.mm"
include "wss.mm"
include "rexr.mm"
include "iocssre.mm"
include "sylancl.mm"
include "c2.mm"
include "caddc.mm"
include "picn.mm"
include "2timesi.mm"
include "oveq2i.mm"
include "negpicn.mm"
include "addcli.mm"
include "addcomi.mm"
include "cmin.mm"
include "negsubi.mm"
include "pncan3oi.mm"
include "eqtri.mm"
include "3eqtrri.mm"
include "efif1olem1.mm"
include "efif1olem2.mm"
include "eff1olem.mm"
include "ax-mp.mm"

theorem eff1o
  let cS: class S
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume eff1o.1: |- S = ( `' Im " ( -u _pi (,] _pi ) )


  assert |- ( exp |` S ) : S -1-1-onto-> ( CC \ { 0 } )

  proof
    cpi
    cneg
    #
    cr
    wcel
    #
    cS
    cc
    cc0
    csn
    cdif
    ce
    cS
    cres
    wf1o
    cpi
    pire
    renegcli
    @1
    vx
    vy
    vz
    vw
    @0
    cpi
    cioc
    co
    #
    cS
    vw
    @2
    ci
    vw
    cv
    cmul
    co
    ce
    cfv
    cmpt
    #
    @3
    eqid
    eff1o.1
    @1
    @0
    cxr
    wcel
    cpi
    cr
    wcel
    @2
    cr
    wss
    @0
    rexr
    pire
    @0
    cpi
    iocssre
    sylancl
    vx
    vy
    @0
    @2
    cpi
    @0
    c2
    cpi
    cmul
    co
    #
    caddc
    co
    #
    @0
    cioc
    @5
    @0
    cpi
    cpi
    caddc
    co
    #
    caddc
    co
    @6
    @0
    caddc
    co
    #
    cpi
    @4
    @6
    @0
    caddc
    cpi
    picn
    2timesi
    oveq2i
    @0
    @6
    negpicn
    cpi
    cpi
    picn
    picn
    addcli
    #
    addcomi
    @7
    @6
    cpi
    cmin
    co
    cpi
    @6
    cpi
    @8
    picn
    negsubi
    cpi
    cpi
    picn
    picn
    pncan3oi
    eqtri
    3eqtrri
    oveq2i
    #
    efif1olem1
    vy
    vz
    @0
    @2
    @9
    efif1olem2
    eff1olem
    ax-mp
end
