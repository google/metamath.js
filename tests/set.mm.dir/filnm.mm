include "clmod.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "clss.mm"
include "wral.mm"
include "clnm.mm"
include "simpl.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "adantl.mm"
include "selpw.mm"
include "sylibr.mm"
include "simplr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "elind.mm"
include "lspid.mm"
include "adantlr.mm"
include "eqcomd.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "islnm2.mm"
include "sylanbrc.mm"

theorem filnm
  let cB: class B
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume filnm.b: |- B = ( Base ` W )


  assert |- ( ( W e. LMod /\ B e. Fin ) -> W e. LNoeM )

  proof
    cW
    clmod
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vb
    cB
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    va
    cW
    clss
    cfv
    #
    wral
    cW
    clnm
    wcel
    @0
    @1
    simpl
    @2
    @10
    va
    @11
    @2
    @3
    @11
    wcel
    #
    wa
    #
    @3
    @9
    wcel
    @3
    @3
    @5
    cfv
    #
    wceq
    #
    @10
    @13
    @8
    cfn
    @3
    @13
    @3
    cB
    wss
    #
    @3
    @8
    wcel
    @12
    @16
    @2
    @11
    @3
    cB
    cW
    filnm.b
    @11
    eqid
    #
    lssss
    adantl
    #
    va
    cB
    selpw
    sylibr
    @13
    @1
    @16
    @3
    cfn
    wcel
    @0
    @1
    @12
    simplr
    @18
    cB
    @3
    ssfi
    syl2anc
    elind
    @13
    @14
    @3
    @0
    @12
    @14
    @3
    wceq
    @1
    @11
    @3
    @5
    cW
    @17
    @5
    eqid
    #
    lspid
    adantlr
    eqcomd
    @7
    @15
    vb
    @3
    @9
    vb
    va
    weq
    @6
    @14
    @3
    @4
    @3
    @5
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    cB
    @11
    vb
    va
    cW
    @5
    filnm.b
    @17
    @19
    islnm2
    sylanbrc
end
