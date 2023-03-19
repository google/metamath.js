include "cops.mm"
include "wcel.mm"
include "cpo.mm"
include "cdm.mm"
include "w3a.mm"
include "cv.mm"
include "coc.mm"
include "cfv.mm"
include "wceq.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "cjn.mm"
include "co.mm"
include "cp1.mm"
include "cmee.mm"
include "cp0.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "isopos.mm"
include "simpl.mm"
include "3adantl1.mm"
include "sylbi.mm"

theorem op01dm
  let cB: class B
  let cU: class U
  let cG: class G
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume op01dm.b: |- B = ( Base ` K )
  assume op01dm.u: |- U = ( lub ` K )
  assume op01dm.g: |- G = ( glb ` K )


  assert |- ( K e. OP -> ( B e. dom U /\ B e. dom G ) )

  proof
    cK
    cops
    wcel
    cK
    cpo
    wcel
    #
    cB
    cU
    cdm
    wcel
    #
    cB
    cG
    cdm
    wcel
    #
    w3a
    vx
    cv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cB
    wcel
    @5
    @4
    cfv
    @3
    wceq
    @3
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    @6
    @4
    cfv
    @5
    @7
    wbr
    wi
    w3a
    @3
    @5
    cK
    cjn
    cfv
    #
    co
    cK
    cp1
    cfv
    #
    wceq
    @3
    @5
    cK
    cmee
    cfv
    #
    co
    cK
    cp0
    cfv
    #
    wceq
    w3a
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    @1
    @2
    wa
    #
    vx
    vy
    cB
    cU
    @9
    cG
    @8
    cK
    @7
    @10
    @4
    @11
    op01dm.b
    op01dm.u
    op01dm.g
    @7
    eqid
    @4
    eqid
    @8
    eqid
    @10
    eqid
    @11
    eqid
    @9
    eqid
    isopos
    @1
    @2
    @12
    @13
    @0
    @13
    @12
    simpl
    3adantl1
    sylbi
end
