include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wrex.mm"
include "lss1.mm"
include "elpwi.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl2an.mm"
include "rabn0.mm"
include "sylibr.mm"
include "lssintcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "lspfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem lspf
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cU: class U
  assume lspval.v: |- V = ( Base ` W )
  assume lspval.s: |- S = ( LSubSp ` W )
  assume lspval.n: |- N = ( LSpan ` W )


  assert |- ( W e. LMod -> N : ~P V --> S )

  proof
    cW
    clmod
    wcel
    #
    cV
    cpw
    #
    cS
    cN
    wf
    @1
    cS
    vs
    @1
    vs
    cv
    #
    vp
    cv
    #
    wss
    #
    vp
    cS
    crab
    #
    cint
    #
    cmpt
    #
    wf
    @0
    vs
    @1
    @6
    cS
    @7
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @0
    @5
    cS
    wss
    #
    @5
    c0
    wne
    #
    @6
    cS
    wcel
    @0
    @8
    simpl
    @10
    @9
    @4
    vp
    cS
    ssrab2
    a1i
    @9
    @4
    vp
    cS
    wrex
    #
    @11
    @0
    cV
    cS
    wcel
    @2
    cV
    wss
    #
    @12
    @8
    cS
    cV
    cW
    lspval.v
    lspval.s
    lss1
    @2
    cV
    elpwi
    @4
    @13
    vp
    cV
    cS
    @3
    cV
    @2
    sseq2
    rspcev
    syl2an
    @4
    vp
    cS
    rabn0
    sylibr
    @5
    cS
    cW
    lspval.s
    lssintcl
    syl3anc
    @7
    eqid
    fmptd
    @0
    @1
    cS
    cN
    @7
    vp
    cS
    cN
    cV
    cW
    clmod
    vs
    lspval.v
    lspval.s
    lspval.n
    lspfval
    feq1d
    mpbird
end
