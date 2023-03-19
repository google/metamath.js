include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "wa.mm"
include "cioo.mm"
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
include "wb.mm"
include "ioon0.mm"
include "syldan.mm"
include "mpbird.mm"
include "df-ioo.mm"
include "cv.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxub.mm"
include "syl3anc.mm"

theorem ioopnfsup
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR* /\ A =/= +oo ) -> sup ( ( A (,) +oo ) , RR* , < ) = +oo )

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
    cioo
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
    @3
    @2
    pnfxr
    a1i
    #
    @2
    @5
    cA
    cpnf
    clt
    wbr
    #
    @0
    @7
    @1
    @0
    @7
    cA
    cpnf
    cA
    nltpnft
    necon2abid
    biimpar
    @0
    @1
    @3
    @5
    @7
    wb
    @6
    cA
    cpnf
    ioon0
    syldan
    mpbird
    vx
    vy
    vz
    vw
    cA
    cpnf
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    vw
    cv
    #
    cxr
    wcel
    #
    @3
    wa
    @8
    cpnf
    clt
    wbr
    idd
    @8
    cpnf
    xrltle
    @0
    @9
    wa
    cA
    @8
    clt
    wbr
    idd
    cA
    @8
    xrltle
    ixxub
    syl3anc
end
