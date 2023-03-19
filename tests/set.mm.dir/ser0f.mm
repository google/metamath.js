include "cz.mm"
include "wcel.mm"
include "caddc.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "ser0.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "eqtr4d.mm"
include "rgen.mm"
include "wfn.mm"
include "wb.mm"
include "cuz.mm"
include "seqfn.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "wf.mm"
include "fconst.mm"
include "ffn.mm"
include "ax-mp.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "mpbiri.mm"

theorem ser0f
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let cN: class N
  assume ser0.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> seq M ( + , ( Z X. { 0 } ) ) = ( Z X. { 0 } ) )

  proof
    cM
    cz
    wcel
    #
    caddc
    cZ
    cc0
    csn
    #
    cxp
    #
    cM
    cseq
    #
    @2
    wceq
    #
    vk
    cv
    #
    @3
    cfv
    #
    @5
    @2
    cfv
    #
    wceq
    #
    vk
    cZ
    wral
    #
    @8
    vk
    cZ
    @5
    cZ
    wcel
    @6
    cc0
    @7
    cM
    @5
    cZ
    ser0.1
    ser0
    cZ
    cc0
    @5
    c0ex
    fvconst2
    eqtr4d
    rgen
    @0
    @3
    cZ
    wfn
    #
    @2
    cZ
    wfn
    #
    @4
    @9
    wb
    @0
    @3
    cM
    cuz
    cfv
    #
    wfn
    @10
    caddc
    @2
    cM
    seqfn
    cZ
    @12
    @3
    ser0.1
    fneq2i
    sylibr
    cZ
    @1
    @2
    wf
    @11
    cZ
    cc0
    c0ex
    fconst
    cZ
    @1
    @2
    ffn
    ax-mp
    vk
    cZ
    @3
    @2
    eqfnfv
    sylancl
    mpbiri
end
