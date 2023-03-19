include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "c0.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "simpl.mm"
include "pnfxr.mm"
include "a1i.mm"
include "wbr.mm"
include "nltpnft.mm"
include "necon2abid.mm"
include "biimpar.mm"
include "lbico1.mm"
include "syl3anc.mm"
include "ne0i.mm"
include "syl.mm"
include "cle.mm"
include "df-ico.mm"
include "cv.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxub.mm"

theorem icopnfsup
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR* /\ A =/= +oo ) -> sup ( ( A [,) +oo ) , RR* , < ) = +oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wne
    #
    wa
    #
    @0
    cpnf
    cxr
    wcel
    #
    cA
    cpnf
    cico
    co
    #
    c0
    wne
    #
    @4
    cxr
    clt
    csup
    cpnf
    wceq
    @0
    @1
    simpl
    #
    @3
    @2
    pnfxr
    a1i
    #
    @2
    cA
    @4
    wcel
    #
    @5
    @2
    @0
    @3
    cA
    cpnf
    clt
    wbr
    #
    @8
    @6
    @7
    @0
    @9
    @1
    @0
    @9
    cA
    cpnf
    cA
    nltpnft
    necon2abid
    biimpar
    cA
    cpnf
    lbico1
    syl3anc
    @4
    cA
    ne0i
    syl
    vx
    vy
    vz
    vw
    cA
    cpnf
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
    vw
    cv
    #
    cxr
    wcel
    #
    @3
    wa
    @10
    cpnf
    clt
    wbr
    idd
    @10
    cpnf
    xrltle
    cA
    @10
    xrltle
    @0
    @11
    wa
    cA
    @10
    cle
    wbr
    idd
    ixxub
    syl3anc
end
