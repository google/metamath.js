include "cpw.mm"
include "clss.mm"
include "cfv.mm"
include "wf.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "clsh.mm"
include "wcel.mm"
include "wa.mm"
include "clsa.mm"
include "wral.mm"
include "wb.mm"
include "eqid.mm"
include "islpolN.mm"
include "syl.mm"
include "mpbid.mm"
include "simpr1.mm"

theorem lpolvN
  let wph: wff ph
  let cP: class P
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume lpolv.v: |- V = ( Base ` W )
  assume lpolv.z: |- .0. = ( 0g ` W )
  assume lpolv.p: |- P = ( LPol ` W )
  assume lpolv.w: |- ( ph -> W e. X )
  assume lpolv.o: |- ( ph -> ._|_ e. P )


  assert |- ( ph -> ( ._|_ ` V ) = { .0. } )

  proof
    wph
    cV
    cpw
    cW
    clss
    cfv
    #
    c.pe
    wf
    #
    cV
    c.pe
    cfv
    c.0
    csn
    wceq
    #
    vx
    cv
    #
    cV
    wss
    vy
    cv
    #
    cV
    wss
    @3
    @4
    wss
    w3a
    @4
    c.pe
    cfv
    @3
    c.pe
    cfv
    #
    wss
    wi
    vy
    wal
    vx
    wal
    #
    @5
    cW
    clsh
    cfv
    #
    wcel
    @5
    c.pe
    cfv
    @3
    wceq
    wa
    vx
    cW
    clsa
    cfv
    #
    wral
    #
    w3a
    wa
    #
    @2
    wph
    c.pe
    cP
    wcel
    #
    @10
    lpolv.o
    wph
    cW
    cX
    wcel
    @11
    @10
    wb
    lpolv.w
    vx
    vy
    @8
    cP
    @0
    @7
    c.pe
    cV
    cW
    cX
    c.0
    lpolv.v
    @0
    eqid
    lpolv.z
    @8
    eqid
    @7
    eqid
    lpolv.p
    islpolN
    syl
    mpbid
    @1
    @2
    @6
    @9
    simpr1
    syl
end
