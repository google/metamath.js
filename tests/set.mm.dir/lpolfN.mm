include "cpw.mm"
include "wf.mm"
include "cfv.mm"
include "c0g.mm"
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
include "simpld.mm"

theorem lpolfN
  let wph: wff ph
  let cP: class P
  let cS: class S
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume lpolf.v: |- V = ( Base ` W )
  assume lpolf.s: |- S = ( LSubSp ` W )
  assume lpolf.p: |- P = ( LPol ` W )
  assume lpolf.w: |- ( ph -> W e. X )
  assume lpolf.o: |- ( ph -> ._|_ e. P )


  assert |- ( ph -> ._|_ : ~P V --> S )

  proof
    wph
    cV
    cpw
    cS
    c.pe
    wf
    #
    cV
    c.pe
    cfv
    cW
    c0g
    cfv
    #
    csn
    wceq
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
    @2
    @3
    wss
    w3a
    @3
    c.pe
    cfv
    @2
    c.pe
    cfv
    #
    wss
    wi
    vy
    wal
    vx
    wal
    @4
    cW
    clsh
    cfv
    #
    wcel
    @4
    c.pe
    cfv
    @2
    wceq
    wa
    vx
    cW
    clsa
    cfv
    #
    wral
    w3a
    #
    wph
    c.pe
    cP
    wcel
    #
    @0
    @7
    wa
    #
    lpolf.o
    wph
    cW
    cX
    wcel
    @8
    @9
    wb
    lpolf.w
    vx
    vy
    @6
    cP
    cS
    @5
    c.pe
    cV
    cW
    cX
    @1
    lpolf.v
    lpolf.s
    @1
    eqid
    @6
    eqid
    @5
    eqid
    lpolf.p
    islpolN
    syl
    mpbid
    simpld
end
