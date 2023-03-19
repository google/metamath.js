include "cdsmm.mm"
include "co.mm"
include "cprds.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "c0g.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfn.mm"
include "wss.mm"
include "ssrab2.mm"
include "eqid.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "dsmmval.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3eqtr4a.mm"
include "wn.mm"
include "c0.mm"
include "ress0.mm"
include "eqcomi.mm"
include "reldmdsmm.mm"
include "ovprc2.mm"
include "reldmprds.mm"
include "oveq1d.mm"
include "pm2.61i.mm"
include "eqtr4i.mm"

theorem dsmmval2
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vx: setvar x
  assume dsmmval2.b: |- B = ( Base ` ( S (+)m R ) )


  assert |- ( S (+)m R ) = ( ( S Xs_ R ) |`s B )

  proof
    cS
    cR
    cdsmm
    co
    #
    cS
    cR
    cprds
    co
    #
    @0
    cbs
    cfv
    #
    cress
    co
    #
    @1
    cB
    cress
    co
    cR
    cvv
    wcel
    #
    @0
    @3
    wceq
    @4
    @1
    vx
    cv
    #
    vf
    cv
    cfv
    @5
    cR
    cfv
    c0g
    cfv
    wne
    vx
    cR
    cdm
    crab
    cfn
    wcel
    #
    vf
    @1
    cbs
    cfv
    #
    crab
    #
    cress
    co
    #
    @1
    @9
    cbs
    cfv
    #
    cress
    co
    @0
    @3
    @8
    @10
    @1
    cress
    @8
    @7
    wss
    @8
    @10
    wceq
    @6
    vf
    @7
    ssrab2
    @8
    @7
    @9
    @1
    @9
    eqid
    @7
    eqid
    ressbas2
    ax-mp
    oveq2i
    vx
    @8
    cR
    cS
    vf
    cvv
    @8
    eqid
    dsmmval
    #
    @4
    @2
    @10
    @1
    cress
    @4
    @0
    @9
    cbs
    @11
    fveq2d
    oveq2d
    3eqtr4a
    @4
    wn
    #
    c0
    c0
    @2
    cress
    co
    #
    @0
    @3
    @13
    c0
    @2
    ress0
    eqcomi
    cS
    cR
    cdsmm
    reldmdsmm
    ovprc2
    @12
    @1
    c0
    @2
    cress
    cS
    cR
    cprds
    reldmprds
    ovprc2
    oveq1d
    3eqtr4a
    pm2.61i
    cB
    @2
    @1
    cress
    dsmmval2.b
    oveq2i
    eqtr4i
end
