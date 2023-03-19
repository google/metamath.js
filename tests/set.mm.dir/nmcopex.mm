include "clo.mm"
include "wcel.mm"
include "ccop.mm"
include "wa.mm"
include "cin.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "elin.mm"
include "cid.mm"
include "chil.mm"
include "cres.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "idlnop.mm"
include "idcnop.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "mpbi.mm"
include "simpli.mm"
include "simpri.mm"
include "nmcopexi.mm"
include "dedth.mm"
include "sylbir.mm"

theorem nmcopex
  let cT: class T


  assert |- ( ( T e. LinOp /\ T e. ContOp ) -> ( normop ` T ) e. RR )

  proof
    cT
    clo
    wcel
    cT
    ccop
    wcel
    wa
    cT
    clo
    ccop
    cin
    #
    wcel
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    cT
    clo
    ccop
    elin
    @1
    @3
    @1
    cT
    cid
    chil
    cres
    #
    cif
    #
    cnop
    cfv
    #
    cr
    wcel
    cT
    @4
    cT
    @5
    wceq
    @2
    @6
    cr
    cT
    @5
    cnop
    fveq2
    eleq1d
    @5
    @5
    clo
    wcel
    #
    @5
    ccop
    wcel
    #
    @5
    @0
    wcel
    @7
    @8
    wa
    cT
    @4
    @0
    @4
    @0
    wcel
    @4
    clo
    wcel
    @4
    ccop
    wcel
    idlnop
    idcnop
    @4
    clo
    ccop
    elin
    mpbir2an
    elimel
    @5
    clo
    ccop
    elin
    mpbi
    #
    simpli
    @7
    @8
    @9
    simpri
    nmcopexi
    dedth
    sylbir
end
