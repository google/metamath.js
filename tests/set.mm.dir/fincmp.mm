include "ctop.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ccmp.mm"
include "inss1.mm"
include "sseli.mm"
include "inss2.mm"
include "wa.mm"
include "vex.mm"
include "pwid.mm"
include "wss.mm"
include "selpw.mm"
include "ssfi.mm"
include "sylan2b.mm"
include "elin.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "sylbir.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "syl.mm"
include "eqid.mm"
include "iscmp.mm"
include "sylanbrc.mm"

theorem fincmp
  let cJ: class J
  let vy: setvar y
  let vz: setvar z


  assert |- ( J e. ( Top i^i Fin ) -> J e. Comp )

  proof
    cJ
    ctop
    cfn
    cin
    #
    wcel
    #
    cJ
    ctop
    wcel
    cJ
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @2
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    @3
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    cJ
    cpw
    #
    wral
    #
    cJ
    ccmp
    wcel
    @0
    ctop
    cJ
    ctop
    cfn
    inss1
    sseli
    @1
    cJ
    cfn
    wcel
    #
    @14
    @0
    cfn
    cJ
    ctop
    cfn
    inss2
    sseli
    @15
    @12
    vy
    @13
    @15
    @3
    @13
    wcel
    #
    wa
    @3
    @9
    wcel
    #
    @3
    cfn
    wcel
    #
    @12
    @3
    vy
    vex
    pwid
    @16
    @15
    @3
    cJ
    wss
    @18
    vy
    cJ
    selpw
    cJ
    @3
    ssfi
    sylan2b
    @17
    @18
    wa
    @3
    @10
    wcel
    #
    @12
    @3
    @9
    cfn
    elin
    @19
    @5
    @11
    @8
    @5
    vz
    @3
    @10
    @6
    @3
    wceq
    @7
    @4
    @2
    @6
    @3
    unieq
    eqeq2d
    rspcev
    ex
    sylbir
    sylancr
    ralrimiva
    syl
    vy
    vz
    cJ
    @2
    @2
    eqid
    iscmp
    sylanbrc
end
