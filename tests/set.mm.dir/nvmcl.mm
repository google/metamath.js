include "cnv.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "nvmf.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem nvmcl
  let cA: class A
  let cB: class B
  let cU: class U
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvmf.1: |- X = ( BaseSet ` U )
  assume nvmf.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) e. X )

  proof
    cU
    cnv
    wcel
    cX
    cX
    cxp
    cX
    cM
    wf
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cM
    co
    cX
    wcel
    cU
    cM
    cX
    nvmf.1
    nvmf.3
    nvmf
    cA
    cB
    cX
    cX
    cX
    cM
    fovrn
    syl3an1
end
