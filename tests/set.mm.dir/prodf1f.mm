include "cz.mm"
include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "prodf1.mm"
include "1ex.mm"
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

theorem prodf1f
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let cN: class N
  assume prodf1.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> seq M ( x. , ( Z X. { 1 } ) ) = ( Z X. { 1 } ) )

  proof
    cM
    cz
    wcel
    #
    cmul
    cZ
    c1
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
    c1
    @7
    cM
    @5
    cZ
    prodf1.1
    prodf1
    cZ
    c1
    @5
    1ex
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
    cmul
    @2
    cM
    seqfn
    cZ
    @12
    @3
    prodf1.1
    fneq2i
    sylibr
    cZ
    @1
    @2
    wf
    @11
    cZ
    c1
    1ex
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
