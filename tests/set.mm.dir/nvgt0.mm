include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "nvz.mm"
include "necon3bid.mm"
include "cr.mm"
include "cle.mm"
include "wb.mm"
include "nvcl.mm"
include "nvge0.mm"
include "ne0gt0.mm"
include "syl2anc.mm"
include "bitr3d.mm"

theorem nvgt0
  let cA: class A
  let cU: class U
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume nvgt0.1: |- X = ( BaseSet ` U )
  assume nvgt0.5: |- Z = ( 0vec ` U )
  assume nvgt0.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( A =/= Z <-> 0 < ( N ` A ) ) )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    wa
    #
    cA
    cN
    cfv
    #
    cc0
    wne
    #
    cA
    cZ
    wne
    cc0
    @1
    clt
    wbr
    #
    @0
    @1
    cc0
    cA
    cZ
    cA
    cU
    cN
    cX
    cZ
    nvgt0.1
    nvgt0.5
    nvgt0.6
    nvz
    necon3bid
    @0
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @2
    @3
    wb
    cA
    cU
    cN
    cX
    nvgt0.1
    nvgt0.6
    nvcl
    cA
    cU
    cN
    cX
    nvgt0.1
    nvgt0.6
    nvge0
    @1
    ne0gt0
    syl2anc
    bitr3d
end
