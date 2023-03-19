include "clo.mm"
include "wcel.mm"
include "ccop.mm"
include "chil.mm"
include "cfv.mm"
include "cno.mm"
include "cnop.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cin.mm"
include "elin.mm"
include "wi.mm"
include "cid.mm"
include "cres.mm"
include "cif.mm"
include "wceq.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "idlnop.mm"
include "idcnop.mm"
include "mpbir2an.mm"
include "elimel.mm"
include "mpbi.mm"
include "simpli.mm"
include "simpri.mm"
include "nmcoplbi.mm"
include "dedth.mm"
include "imp.mm"
include "sylanbr.mm"
include "3impa.mm"

theorem nmcoplb
  let cA: class A
  let cT: class T


  assert |- ( ( T e. LinOp /\ T e. ContOp /\ A e. ~H ) -> ( normh ` ( T ` A ) ) <_ ( ( normop ` T ) x. ( normh ` A ) ) )

  proof
    cT
    clo
    wcel
    #
    cT
    ccop
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cno
    cfv
    #
    cT
    cnop
    cfv
    #
    cA
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    wa
    cT
    clo
    ccop
    cin
    #
    wcel
    #
    @2
    @8
    cT
    clo
    ccop
    elin
    @10
    @2
    @8
    @10
    @2
    @8
    wi
    @2
    cA
    @10
    cT
    cid
    chil
    cres
    #
    cif
    #
    cfv
    #
    cno
    cfv
    #
    @12
    cnop
    cfv
    #
    @6
    cmul
    co
    #
    cle
    wbr
    #
    wi
    cT
    @11
    cT
    @12
    wceq
    #
    @8
    @17
    @2
    @18
    @4
    @14
    @7
    @16
    cle
    @18
    @3
    @13
    cno
    cA
    cT
    @12
    fveq1
    fveq2d
    @18
    @5
    @15
    @6
    cmul
    cT
    @12
    cnop
    fveq2
    oveq1d
    breq12d
    imbi2d
    cA
    @12
    @12
    clo
    wcel
    #
    @12
    ccop
    wcel
    #
    @12
    @9
    wcel
    @19
    @20
    wa
    cT
    @11
    @9
    @11
    @9
    wcel
    @11
    clo
    wcel
    @11
    ccop
    wcel
    idlnop
    idcnop
    @11
    clo
    ccop
    elin
    mpbir2an
    elimel
    @12
    clo
    ccop
    elin
    mpbi
    #
    simpli
    @19
    @20
    @21
    simpri
    nmcoplbi
    dedth
    imp
    sylanbr
    3impa
end
