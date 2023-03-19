include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "cntzrcl.mm"
include "simprd.mm"
include "eqid.mm"
include "cntzval.mm"
include "syl.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "pm2.61ine.mm"

theorem cntzssv
  let cB: class B
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume cntzrcl.b: |- B = ( Base ` M )
  assume cntzrcl.z: |- Z = ( Cntz ` M )


  assert |- ( Z ` S ) C_ B

  proof
    cS
    cZ
    cfv
    #
    cB
    wss
    #
    @0
    c0
    @0
    c0
    wceq
    @1
    c0
    cB
    wss
    cB
    0ss
    @0
    c0
    cB
    sseq1
    mpbiri
    @0
    c0
    wne
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @1
    vx
    @0
    n0
    @3
    @1
    vx
    @3
    @0
    @2
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    @4
    @2
    @5
    co
    wceq
    vy
    cS
    wral
    #
    vx
    cB
    crab
    #
    cB
    @3
    cS
    cB
    wss
    #
    @0
    @7
    wceq
    @3
    cM
    cvv
    wcel
    @8
    cB
    cS
    cM
    @2
    cZ
    cntzrcl.b
    cntzrcl.z
    cntzrcl
    simprd
    vx
    vy
    cB
    @5
    cS
    cM
    cZ
    cntzrcl.b
    @5
    eqid
    cntzrcl.z
    cntzval
    syl
    @6
    vx
    cB
    ssrab2
    syl6eqss
    exlimiv
    sylbi
    pm2.61ine
end
