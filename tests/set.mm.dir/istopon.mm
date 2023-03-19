include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "elfvex.mm"
include "uniexg.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "cv.mm"
include "crab.mm"
include "eqeq1.mm"
include "rabbidv.mm"
include "df-topon.mm"
include "cpw.mm"
include "vpwex.mm"
include "pwex.mm"
include "wss.mm"
include "wi.mm"
include "rabss.mm"
include "pwuni.mm"
include "pweq.mm"
include "syl5sseqr.mm"
include "selpw.mm"
include "sylibr.mm"
include "a1i.mm"
include "mprgbir.mm"
include "ssexi.mm"
include "fvmpt3i.mm"
include "eleq2d.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem istopon
  let cB: class B
  let cJ: class J
  let vb: setvar b
  let vj: setvar j


  assert |- ( J e. ( TopOn ` B ) <-> ( J e. Top /\ B = U. J ) )

  proof
    cJ
    cB
    ctopon
    cfv
    #
    wcel
    #
    cB
    cvv
    wcel
    #
    cJ
    ctop
    wcel
    #
    cB
    cJ
    cuni
    #
    wceq
    #
    wa
    #
    cJ
    cB
    ctopon
    elfvex
    @3
    @5
    @2
    @3
    @2
    @5
    @4
    cvv
    wcel
    cJ
    ctop
    uniexg
    cB
    @4
    cvv
    eleq1
    syl5ibrcom
    imp
    @2
    @1
    cJ
    cB
    vj
    cv
    #
    cuni
    #
    wceq
    #
    vj
    ctop
    crab
    #
    wcel
    @6
    @2
    @0
    @10
    cJ
    vb
    cB
    vb
    cv
    #
    @8
    wceq
    #
    vj
    ctop
    crab
    #
    @10
    cvv
    ctopon
    @11
    cB
    wceq
    @12
    @9
    vj
    ctop
    @11
    cB
    @8
    eqeq1
    rabbidv
    vj
    vb
    df-topon
    @13
    @11
    cpw
    #
    cpw
    #
    @14
    vb
    vpwex
    pwex
    @13
    @15
    wss
    @12
    @7
    @15
    wcel
    #
    wi
    #
    vj
    ctop
    @12
    vj
    ctop
    @15
    rabss
    @17
    @7
    ctop
    wcel
    @12
    @7
    @14
    wss
    @16
    @12
    @8
    cpw
    @7
    @14
    @7
    pwuni
    @11
    @8
    pweq
    syl5sseqr
    vj
    @14
    selpw
    sylibr
    a1i
    mprgbir
    ssexi
    fvmpt3i
    eleq2d
    @9
    @5
    vj
    cJ
    ctop
    @7
    cJ
    wceq
    @8
    @4
    cB
    @7
    cJ
    unieq
    eqeq2d
    elrab
    syl6bb
    pm5.21nii
end
