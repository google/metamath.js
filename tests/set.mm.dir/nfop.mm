include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cpr.mm"
include "c0.mm"
include "cif.mm"
include "dfopif.mm"
include "nfel1.mm"
include "nfan.mm"
include "nfsn.mm"
include "nfpr.mm"
include "nfcv.mm"
include "nfif.mm"
include "nfcxfr.mm"

theorem nfop
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfop.1: |- F/_ x A
  assume nfop.2: |- F/_ x B


  assert |- F/_ x <. A , B >.

  proof
    vx
    cA
    cB
    cop
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    c0
    cif
    cA
    cB
    dfopif
    @2
    vx
    @5
    c0
    @0
    @1
    vx
    vx
    cA
    cvv
    nfop.1
    nfel1
    vx
    cB
    cvv
    nfop.2
    nfel1
    nfan
    vx
    @3
    @4
    vx
    cA
    nfop.1
    nfsn
    vx
    cA
    cB
    nfop.1
    nfop.2
    nfpr
    nfpr
    vx
    c0
    nfcv
    nfif
    nfcxfr
end
