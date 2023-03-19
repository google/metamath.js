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
include "djafvalN.mm"
include "adantr.mm"
include "oveqd.mm"
include "cvv.mm"
include "cltrn.mm"
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

theorem djavalN
  let cT: class T
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume djaval.h: |- H = ( LHyp ` K )
  assume djaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume djaval.i: |- I = ( ( DIsoA ` K ) ` W )
  assume djaval.n: |- ._|_ = ( ( ocA ` K ) ` W )
  assume djaval.j: |- J = ( ( vA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X C_ T /\ Y C_ T ) ) -> ( X J Y ) = ( ._|_ ` ( ( ._|_ ` X ) i^i ( ._|_ ` Y ) ) ) )

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
    cT
    wss
    #
    cY
    cT
    wss
    #
    wa
    #
    wa
    #
    cX
    cY
    cJ
    co
    cX
    cY
    vx
    vy
    cT
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
    cJ
    @12
    cX
    cY
    @0
    cJ
    @12
    wceq
    @3
    vx
    vy
    cT
    cH
    cI
    cJ
    cK
    c.pe
    chlt
    cW
    djaval.h
    djaval.t
    djaval.i
    djaval.n
    djaval.j
    djafvalN
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
    cT
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    djaval.t
    cW
    @20
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
    cT
    @21
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
    @22
    c.pe
    @23
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
    @22
    @16
    c.pe
    @24
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
