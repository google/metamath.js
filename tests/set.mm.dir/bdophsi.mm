include "chos.mm"
include "co.mm"
include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "bdopln.mm"
include "ax-mp.mm"
include "lnophsi.mm"
include "cxr.mm"
include "caddc.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "chil.mm"
include "wf.mm"
include "bdopf.mm"
include "hoaddcli.mm"
include "nmopxr.mm"
include "nmopre.mm"
include "readdcli.mm"
include "nmopgtmnf.mm"
include "nmoptrii.mm"
include "xrre.mm"
include "mp4an.mm"
include "elbdop2.mm"
include "mpbir2an.mm"

theorem bdophsi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( S +op T ) e. BndLinOp

  proof
    cS
    cT
    chos
    co
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
    lnophsi
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
    caddc
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
    @8
    cle
    wbr
    @2
    chil
    chil
    @0
    wf
    #
    @5
    cS
    cT
    @3
    chil
    chil
    cS
    wf
    nmoptri.1
    cS
    bdopf
    ax-mp
    @4
    chil
    chil
    cT
    wf
    nmoptri.2
    cT
    bdopf
    ax-mp
    hoaddcli
    #
    @0
    nmopxr
    ax-mp
    @6
    @7
    @3
    @6
    cr
    wcel
    nmoptri.1
    cS
    nmopre
    ax-mp
    @4
    @7
    cr
    wcel
    nmoptri.2
    cT
    nmopre
    ax-mp
    readdcli
    @10
    @9
    @11
    @0
    nmopgtmnf
    ax-mp
    cS
    cT
    nmoptri.1
    nmoptri.2
    nmoptrii
    @1
    @8
    xrre
    mp4an
    @0
    elbdop2
    mpbir2an
end
