include "ccnfld.mm"
include "crg.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "c1.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "cnring.mm"
include "difss.mm"
include "wne.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "w3a.mm"
include "cnfldbas.mm"
include "cnfld1.mm"
include "ringidss.mm"
include "eqcomd.mm"
include "mp3an.mm"

theorem cnmgpid
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cnmgpabl.m: |- M = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )


  assert |- ( 0g ` M ) = 1

  proof
    ccnfld
    crg
    wcel
    #
    cc
    cc0
    csn
    #
    cdif
    #
    cc
    wss
    #
    c1
    @2
    wcel
    #
    cM
    c0g
    cfv
    #
    c1
    wceq
    cnring
    cc
    @1
    difss
    @4
    c1
    cc
    wcel
    c1
    cc0
    wne
    ax-1cn
    ax-1ne0
    c1
    cc
    cc0
    eldifsn
    mpbir2an
    @0
    @3
    @4
    w3a
    c1
    @5
    @2
    cc
    ccnfld
    c1
    cM
    cnmgpabl.m
    cnfldbas
    cnfld1
    ringidss
    eqcomd
    mp3an
end
