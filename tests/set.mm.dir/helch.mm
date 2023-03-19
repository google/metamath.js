include "chil.mm"
include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "c0v.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "ssid.mm"
include "ax-hv0cl.mm"
include "pm3.2i.mm"
include "hvaddcl.mm"
include "rgen2a.mm"
include "hvmulcl.mm"
include "rgen2.mm"
include "issh2.mm"
include "mpbir2an.mm"
include "vex.mm"
include "hlimveci.mm"
include "adantl.mm"
include "gen2.mm"
include "isch2.mm"

theorem helch
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ~H e. CH

  proof
    chil
    cch
    wcel
    chil
    csh
    wcel
    #
    cn
    chil
    vf
    cv
    #
    wf
    #
    @1
    vx
    cv
    #
    chli
    wbr
    #
    wa
    @3
    chil
    wcel
    #
    wi
    #
    vx
    wal
    vf
    wal
    @0
    chil
    chil
    wss
    #
    c0v
    chil
    wcel
    #
    wa
    @3
    vy
    cv
    #
    cva
    co
    chil
    wcel
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @3
    @9
    csm
    co
    chil
    wcel
    #
    vy
    chil
    wral
    vx
    cc
    wral
    #
    wa
    @7
    @8
    chil
    ssid
    ax-hv0cl
    pm3.2i
    @11
    @13
    @10
    vx
    vy
    chil
    @3
    @9
    hvaddcl
    rgen2a
    @12
    vx
    vy
    cc
    chil
    @3
    @9
    hvmulcl
    rgen2
    pm3.2i
    vx
    vy
    chil
    issh2
    mpbir2an
    @6
    vf
    vx
    @4
    @5
    @2
    @3
    @1
    vx
    vex
    hlimveci
    adantl
    gen2
    vx
    vf
    chil
    isch2
    mpbir2an
end
