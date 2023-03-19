include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "wb.mm"
include "dmresi.mm"
include "f1eq2.mm"
include "mpbir.mm"
include "eqcomi.mm"
include "f1eq3.mm"
include "mp1i.mm"
include "mpbiri.mm"

theorem usgrexilem
  let vx: setvar x
  let cP: class P
  let cV: class V
  let cW: class W
  assume usgrexi.p: |- P = { x e. ~P V | ( # ` x ) = 2 }

  disjoint V x
  assert |- ( V e. W -> ( _I |` P ) : dom ( _I |` P ) -1-1-> { x e. ~P V | ( # ` x ) = 2 } )

  proof
    cV
    cW
    wcel
    #
    cid
    cP
    cres
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    crab
    #
    @1
    wf1
    #
    @2
    cP
    @1
    wf1
    #
    @5
    cP
    cP
    @1
    wf1
    #
    cP
    cP
    @1
    wf1o
    @6
    cP
    f1oi
    cP
    cP
    @1
    f1of1
    ax-mp
    @2
    cP
    wceq
    @5
    @6
    wb
    cP
    dmresi
    @2
    cP
    cP
    @1
    f1eq2
    ax-mp
    mpbir
    @3
    cP
    wceq
    @4
    @5
    wb
    @0
    cP
    @3
    usgrexi.p
    eqcomi
    @3
    cP
    @2
    @1
    f1eq3
    mp1i
    mpbiri
end
