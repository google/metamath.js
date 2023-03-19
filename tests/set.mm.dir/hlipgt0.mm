include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "wne.mm"
include "cc0.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "hlnv.mm"
include "w3a.mm"
include "cnmcv.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cr.mm"
include "eqid.mm"
include "nvcl.mm"
include "3adant3.mm"
include "wa.mm"
include "wceq.mm"
include "nvz.mm"
include "biimpd.mm"
include "necon3d.mm"
include "3impia.mm"
include "sqgt0d.mm"
include "ipidsq.mm"
include "breqtrrd.mm"
include "syl3an1.mm"

theorem hlipgt0
  let cA: class A
  let cP: class P
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume hlipgt0.1: |- X = ( BaseSet ` U )
  assume hlipgt0.5: |- Z = ( 0vec ` U )
  assume hlipgt0.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X /\ A =/= Z ) -> 0 < ( A P A ) )

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cZ
    wne
    #
    cc0
    cA
    cA
    cP
    co
    #
    clt
    wbr
    cU
    hlnv
    @0
    @1
    @2
    w3a
    #
    cc0
    cA
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    #
    @3
    clt
    @4
    @6
    @0
    @1
    @6
    cr
    wcel
    @2
    cA
    cU
    @5
    cX
    hlipgt0.1
    @5
    eqid
    #
    nvcl
    3adant3
    @0
    @1
    @2
    @6
    cc0
    wne
    @0
    @1
    wa
    #
    @6
    cc0
    cA
    cZ
    @9
    @6
    cc0
    wceq
    cA
    cZ
    wceq
    cA
    cU
    @5
    cX
    cZ
    hlipgt0.1
    hlipgt0.5
    @8
    nvz
    biimpd
    necon3d
    3impia
    sqgt0d
    @0
    @1
    @3
    @7
    wceq
    @2
    cA
    cP
    cU
    @5
    cX
    hlipgt0.1
    @8
    hlipgt0.7
    ipidsq
    3adant3
    breqtrrd
    syl3an1
end
