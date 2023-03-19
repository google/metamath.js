include "ccom.mm"
include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "bdopln.mm"
include "ax-mp.mm"
include "lnopcoi.mm"
include "cxr.mm"
include "cmul.mm"
include "co.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "chil.mm"
include "wf.mm"
include "lnopfi.mm"
include "hocofi.mm"
include "nmopxr.mm"
include "nmopre.mm"
include "remulcli.mm"
include "nmopgtmnf.mm"
include "nmopcoi.mm"
include "xrre.mm"
include "mp4an.mm"
include "elbdop2.mm"
include "mpbir2an.mm"

theorem bdopcoi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( S o. T ) e. BndLinOp

  proof
    cS
    cT
    ccom
    #
    cbo
    wcel
    @0
    clo
    wcel
    @0
    cnop
    cfv
    #
    cr
    wcel
    #
    cS
    cT
    cS
    cbo
    wcel
    #
    cS
    clo
    wcel
    nmoptri.1
    cS
    bdopln
    ax-mp
    #
    cT
    cbo
    wcel
    #
    cT
    clo
    wcel
    nmoptri.2
    cT
    bdopln
    ax-mp
    #
    lnopcoi
    @1
    cxr
    wcel
    #
    cS
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    cmul
    co
    #
    cr
    wcel
    cmnf
    @1
    clt
    wbr
    #
    @1
    @10
    cle
    wbr
    @2
    chil
    chil
    @0
    wf
    #
    @7
    cS
    cT
    cS
    @4
    lnopfi
    cT
    @6
    lnopfi
    hocofi
    #
    @0
    nmopxr
    ax-mp
    @8
    @9
    @3
    @8
    cr
    wcel
    nmoptri.1
    cS
    nmopre
    ax-mp
    @5
    @9
    cr
    wcel
    nmoptri.2
    cT
    nmopre
    ax-mp
    remulcli
    @12
    @11
    @13
    @0
    nmopgtmnf
    ax-mp
    cS
    cT
    nmoptri.1
    nmoptri.2
    nmopcoi
    @1
    @10
    xrre
    mp4an
    @0
    elbdop2
    mpbir2an
end
