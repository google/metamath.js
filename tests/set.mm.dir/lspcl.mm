include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "cfv.mm"
include "wss.mm"
include "lspf.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "ffvelrn.mm"
include "syl2an.mm"

theorem lspcl
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  assume lspval.v: |- V = ( Base ` W )
  assume lspval.s: |- S = ( LSubSp ` W )
  assume lspval.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U C_ V ) -> ( N ` U ) e. S )

  proof
    cW
    clmod
    wcel
    cV
    cpw
    #
    cS
    cN
    wf
    cU
    @0
    wcel
    #
    cU
    cN
    cfv
    cS
    wcel
    cU
    cV
    wss
    #
    cS
    cN
    cV
    cW
    lspval.v
    lspval.s
    lspval.n
    lspf
    @1
    @2
    cU
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lspval.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    biimpri
    @0
    cS
    cU
    cN
    ffvelrn
    syl2an
end
