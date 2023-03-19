include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cbs.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "cvv.mm"
include "eqid.mm"
include "cntzrcl.mm"
include "simprd.mm"
include "elcntz.mm"
include "syl.mm"
include "simplbda.mm"
include "anidms.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem cntzi
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  assume cntzi.p: |- .+ = ( +g ` M )
  assume cntzi.z: |- Z = ( Cntz ` M )


  assert |- ( ( X e. ( Z ` S ) /\ Y e. S ) -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    cX
    cS
    cZ
    cfv
    wcel
    #
    cX
    vy
    cv
    #
    c.pl
    co
    #
    @1
    cX
    c.pl
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    cY
    cS
    wcel
    cX
    cY
    c.pl
    co
    #
    cY
    cX
    c.pl
    co
    #
    wceq
    #
    @0
    @5
    @0
    @0
    cX
    cM
    cbs
    cfv
    #
    wcel
    #
    @5
    @0
    cS
    @9
    wss
    #
    @0
    @10
    @5
    wa
    wb
    @0
    cM
    cvv
    wcel
    @11
    @9
    cS
    cM
    cX
    cZ
    @9
    eqid
    #
    cntzi.z
    cntzrcl
    simprd
    vy
    cX
    @9
    c.pl
    cS
    cM
    cZ
    @12
    cntzi.p
    cntzi.z
    elcntz
    syl
    simplbda
    anidms
    @4
    @8
    vy
    cY
    cS
    @1
    cY
    wceq
    @2
    @6
    @3
    @7
    @1
    cY
    cX
    c.pl
    oveq2
    @1
    cY
    cX
    c.pl
    oveq1
    eqeq12d
    rspccva
    sylan
end
