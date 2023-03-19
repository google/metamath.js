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
include "simpl.mm"
include "syl56.mm"
include "mpd.mm"

theorem lpolsatN
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cH: class H
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume lpolsat.a: |- A = ( LSAtoms ` W )
  assume lpolsat.h: |- H = ( LSHyp ` W )
  assume lpolsat.p: |- P = ( LPol ` W )
  assume lpolsat.w: |- ( ph -> W e. X )
  assume lpolsat.o: |- ( ph -> ._|_ e. P )
  assume lpolsat.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( ._|_ ` Q ) e. H )

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
    cH
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
    cH
    wcel
    #
    wph
    c.pe
    cP
    wcel
    #
    @14
    lpolsat.o
    wph
    cW
    cX
    wcel
    @17
    @14
    wb
    lpolsat.w
    vx
    vy
    cA
    cP
    @1
    cH
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
    lpolsat.a
    lpolsat.h
    lpolsat.p
    islpolN
    syl
    mpbid
    @14
    @13
    wph
    @16
    @15
    c.pe
    cfv
    #
    cQ
    wceq
    #
    wa
    #
    @16
    @2
    @4
    @8
    @13
    simpr3
    wph
    cQ
    cA
    wcel
    @13
    @20
    wi
    lpolsat.q
    @12
    @20
    vx
    cQ
    cA
    @5
    cQ
    wceq
    #
    @9
    @16
    @11
    @19
    @21
    @7
    @15
    cH
    @5
    cQ
    c.pe
    fveq2
    #
    eleq1d
    @21
    @10
    @18
    @5
    cQ
    @21
    @7
    @15
    c.pe
    @22
    fveq2d
    @21
    id
    eqeq12d
    anbi12d
    rspcv
    syl
    @16
    @19
    simpl
    syl56
    mpd
end
