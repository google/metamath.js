include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "co.mm"
include "cpw.mm"
include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "cmpt2.mm"
include "wceq.mm"
include "djhfval.mm"
include "adantr.mm"
include "oveqd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "fvexd.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "fveq2d.mm"
include "ineq2d.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem djhval
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume djhval.h: |- H = ( LHyp ` K )
  assume djhval.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhval.v: |- V = ( Base ` U )
  assume djhval.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume djhval.j: |- .\/ = ( ( joinH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X C_ V /\ Y C_ V ) ) -> ( X .\/ Y ) = ( ._|_ ` ( ( ._|_ ` X ) i^i ( ._|_ ` Y ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    cY
    cV
    wss
    #
    wa
    #
    wa
    #
    cX
    cY
    c.or
    co
    cX
    cY
    vx
    vy
    cV
    cpw
    #
    @5
    vx
    cv
    #
    c.pe
    cfv
    #
    vy
    cv
    #
    c.pe
    cfv
    #
    cin
    #
    c.pe
    cfv
    #
    cmpt2
    #
    co
    #
    cX
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    cin
    #
    c.pe
    cfv
    #
    @4
    c.or
    @12
    cX
    cY
    @0
    c.or
    @12
    wceq
    @3
    vx
    vy
    cU
    cH
    c.or
    cK
    c.pe
    cV
    cW
    chlt
    djhval.h
    djhval.u
    djhval.v
    djhval.o
    djhval.j
    djhfval
    adantr
    oveqd
    @4
    cX
    @5
    wcel
    #
    cY
    @5
    wcel
    #
    @17
    cvv
    wcel
    @13
    @17
    wceq
    @1
    @18
    @0
    @2
    @18
    @1
    cX
    cV
    cV
    cU
    cbs
    cfv
    cvv
    djhval.v
    cU
    cbs
    fvex
    eqeltri
    #
    elpw2
    biimpri
    ad2antrl
    @2
    @19
    @0
    @1
    @19
    @2
    cY
    cV
    @20
    elpw2
    biimpri
    ad2antll
    @4
    @16
    c.pe
    fvexd
    vx
    vy
    cX
    cY
    @5
    @5
    @11
    @17
    @12
    @14
    @9
    cin
    #
    c.pe
    cfv
    cvv
    @6
    cX
    wceq
    #
    @10
    @21
    c.pe
    @22
    @7
    @14
    @9
    @6
    cX
    c.pe
    fveq2
    ineq1d
    fveq2d
    @8
    cY
    wceq
    #
    @21
    @16
    c.pe
    @23
    @9
    @15
    @14
    @8
    cY
    c.pe
    fveq2
    ineq2d
    fveq2d
    @12
    eqid
    ovmpt2g
    syl3anc
    eqtrd
end
