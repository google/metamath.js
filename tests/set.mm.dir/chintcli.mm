include "cint.mm"
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
include "c0.mm"
include "wne.mm"
include "simpli.mm"
include "chsssh.mm"
include "sstri.mm"
include "simpri.mm"
include "pm3.2i.mm"
include "shintcli.mm"
include "wral.mm"
include "sseli.mm"
include "vex.mm"
include "chlimi.mm"
include "3exp.mm"
include "com3r.mm"
include "syl5.mm"
include "imp.mm"
include "ralimdva.mm"
include "fint.mm"
include "elint2.mm"
include "3imtr4g.mm"
include "impcom.mm"
include "gen2.mm"
include "isch2.mm"
include "mpbir2an.mm"

theorem chintcli
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  assume chintcl.1: |- ( A C_ CH /\ A =/= (/) )


  assert |- |^| A e. CH

  proof
    cA
    cint
    #
    cch
    wcel
    @0
    csh
    wcel
    cn
    @0
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
    @0
    wcel
    #
    wi
    #
    vx
    wal
    vf
    wal
    cA
    cA
    csh
    wss
    cA
    c0
    wne
    #
    cA
    cch
    csh
    cA
    cch
    wss
    #
    @7
    chintcl.1
    simpli
    #
    chsssh
    sstri
    @8
    @7
    chintcl.1
    simpri
    #
    pm3.2i
    shintcli
    @6
    vf
    vx
    @4
    @2
    @5
    @4
    cn
    vy
    cv
    #
    @1
    wf
    #
    vy
    cA
    wral
    @3
    @11
    wcel
    #
    vy
    cA
    wral
    @2
    @5
    @4
    @12
    @13
    vy
    cA
    @4
    @11
    cA
    wcel
    #
    @12
    @13
    wi
    #
    @14
    @11
    cch
    wcel
    #
    @4
    @15
    cA
    cch
    @11
    @9
    sseli
    @16
    @12
    @4
    @13
    @16
    @12
    @4
    @13
    @3
    @1
    @11
    vx
    vex
    #
    chlimi
    3exp
    com3r
    syl5
    imp
    ralimdva
    vy
    cn
    cA
    @1
    @10
    fint
    vy
    @3
    cA
    @17
    elint2
    3imtr4g
    impcom
    gen2
    vx
    vf
    @0
    isch2
    mpbir2an
end
