include "cwwlksnon.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "rgen2w.mm"
include "cc0.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "crab.mm"
include "df-wwlksnon.mm"
include "fveq2.mm"
include "jca.mm"
include "adantl.mm"
include "el2mpt2cl.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "biimpri.mm"
include "simpl2im.mm"

theorem wwlksonvtx
  let cA: class A
  let cC: class C
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  assume wwlksonvtx.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( A ( N WWalksNOn G ) C ) -> ( A e. V /\ C e. V ) )

  proof
    cW
    cA
    cC
    cN
    cG
    cwwlksnon
    co
    co
    wcel
    #
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cC
    @2
    wcel
    #
    wa
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    vg
    cv
    #
    cvtx
    cfv
    #
    cvv
    wcel
    #
    @11
    wa
    #
    vg
    cvv
    wral
    vn
    cn0
    wral
    @0
    @1
    @5
    wa
    wi
    @12
    vn
    vg
    cn0
    cvv
    @11
    @11
    @9
    cvtx
    fvex
    #
    @13
    pm3.2i
    rgen2w
    vn
    vg
    vb
    cn0
    cvv
    @10
    @10
    cA
    cC
    cvv
    cc0
    vw
    cv
    #
    cfv
    va
    cv
    wceq
    vn
    cv
    #
    @14
    cfv
    vb
    cv
    wceq
    wa
    vw
    @15
    @9
    cwwlksn
    co
    crab
    @2
    @2
    cwwlksnon
    cvv
    cW
    cN
    cG
    va
    vw
    vg
    vn
    va
    vb
    df-wwlksnon
    @9
    cG
    wceq
    #
    @10
    @2
    wceq
    #
    @17
    wa
    @15
    cN
    wceq
    @16
    @17
    @17
    @9
    cG
    cvtx
    fveq2
    #
    @18
    jca
    adantl
    el2mpt2cl
    ax-mp
    @8
    @5
    @6
    @3
    @7
    @4
    cV
    @2
    cA
    wwlksonvtx.v
    eleq2i
    cV
    @2
    cC
    wwlksonvtx.v
    eleq2i
    anbi12i
    biimpri
    simpl2im
end
