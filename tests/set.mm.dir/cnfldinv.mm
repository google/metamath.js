include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "ccnfld.mm"
include "cinvr.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "eldifsn.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "cnflddiv.mm"
include "cnfld1.mm"
include "eqid.mm"
include "ringinvdv.mm"
include "mpan.mm"
include "sylbir.mm"

theorem cnfldinv
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( ( X e. CC /\ X =/= 0 ) -> ( ( invr ` CCfld ) ` X ) = ( 1 / X ) )

  proof
    cX
    cc
    wcel
    cX
    cc0
    wne
    wa
    cX
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    cX
    ccnfld
    cinvr
    cfv
    #
    cfv
    c1
    cX
    cdiv
    co
    wceq
    #
    cX
    cc
    cc0
    eldifsn
    ccnfld
    crg
    wcel
    @1
    @3
    cnring
    cc
    cdiv
    ccnfld
    @0
    c1
    @2
    cX
    cnfldbas
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    cnflddiv
    cnfld1
    @2
    eqid
    ringinvdv
    mpan
    sylbir
end
