include "cc.mm"
include "cv.mm"
include "cmr.mm"
include "co.mm"
include "cm1r.mm"
include "cplr.mm"
include "cmul.mm"
include "cep.mm"
include "ccnv.mm"
include "cnr.mm"
include "dfcnqs.mm"
include "mulcnsrec.mm"
include "mulcomsr.mm"
include "oveq2i.mm"
include "oveq12i.mm"
include "addcomsr.mm"
include "eqtri.mm"
include "ecovcom.mm"

theorem axmulcom
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A x. B ) = ( B x. A ) )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cc
    vx
    cv
    #
    vz
    cv
    #
    cmr
    co
    #
    cm1r
    vy
    cv
    #
    vw
    cv
    #
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    cmul
    cep
    ccnv
    cnr
    @3
    @1
    cmr
    co
    #
    @0
    @4
    cmr
    co
    #
    cplr
    co
    #
    @1
    @0
    cmr
    co
    #
    cm1r
    @4
    @3
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    @4
    @0
    cmr
    co
    #
    @1
    @3
    cmr
    co
    #
    cplr
    co
    #
    dfcnqs
    @0
    @3
    @1
    @4
    mulcnsrec
    @1
    @4
    @0
    @3
    mulcnsrec
    @2
    @10
    @6
    @12
    cplr
    @0
    @1
    mulcomsr
    @5
    @11
    cm1r
    cmr
    @3
    @4
    mulcomsr
    oveq2i
    oveq12i
    @9
    @14
    @13
    cplr
    co
    @15
    @7
    @14
    @8
    @13
    cplr
    @3
    @1
    mulcomsr
    @0
    @4
    mulcomsr
    oveq12i
    @14
    @13
    addcomsr
    eqtri
    ecovcom
end
