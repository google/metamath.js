include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "clss.mm"
include "wf.mm"
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
include "wral.mm"
include "wb.mm"
include "eqid.mm"
include "islpolN.mm"
include "syl.mm"
include "mpbid.mm"
include "simpr3.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "simpr.mm"
include "syl56.mm"
include "mpd.mm"

theorem lpolpolsatN
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume lpolpolsat.a: |- A = ( LSAtoms ` W )
  assume lpolpolsat.p: |- P = ( LPol ` W )
  assume lpolpolsat.w: |- ( ph -> W e. X )
  assume lpolpolsat.o: |- ( ph -> ._|_ e. P )
  assume lpolpolsat.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` Q ) ) = Q )

  proof
    wph
    cW
    cbs
    cfv
    #
    cpw
    cW
    clss
    cfv
    #
    c.pe
    wf
    #
    @0
    c.pe
    cfv
    cW
    c0g
    cfv
    #
    csn
    wceq
    #
    vx
    cv
    #
    @0
    wss
    vy
    cv
    #
    @0
    wss
    @5
    @6
    wss
    w3a
    @6
    c.pe
    cfv
    @5
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
    @7
    cW
    clsh
    cfv
    #
    wcel
    #
    @7
    c.pe
    cfv
    #
    @5
    wceq
    #
    wa
    #
    vx
    cA
    wral
    #
    w3a
    wa
    #
    cQ
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cQ
    wceq
    #
    wph
    c.pe
    cP
    wcel
    #
    @15
    lpolpolsat.o
    wph
    cW
    cX
    wcel
    @19
    @15
    wb
    lpolpolsat.w
    vx
    vy
    cA
    cP
    @1
    @9
    c.pe
    @0
    cW
    cX
    @3
    @0
    eqid
    @1
    eqid
    @3
    eqid
    lpolpolsat.a
    @9
    eqid
    lpolpolsat.p
    islpolN
    syl
    mpbid
    @15
    @14
    wph
    @16
    @9
    wcel
    #
    @18
    wa
    #
    @18
    @2
    @4
    @8
    @14
    simpr3
    wph
    cQ
    cA
    wcel
    @14
    @21
    wi
    lpolpolsat.q
    @13
    @21
    vx
    cQ
    cA
    @5
    cQ
    wceq
    #
    @10
    @20
    @12
    @18
    @22
    @7
    @16
    @9
    @5
    cQ
    c.pe
    fveq2
    #
    eleq1d
    @22
    @11
    @17
    @5
    cQ
    @22
    @7
    @16
    c.pe
    @23
    fveq2d
    @22
    id
    eqeq12d
    anbi12d
    rspcv
    syl
    @20
    @18
    simpr
    syl56
    mpd
end
