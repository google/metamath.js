include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "cvtx.mm"
include "wa.mm"
include "cn0.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cfz.mm"
include "wral.mm"
include "wwlknbp1.mm"
include "wwlknvtx.mm"
include "wi.mm"
include "0elfz.mm"
include "wb.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "adantl.mm"
include "rspcdv.mm"
include "nn0fz0.mm"
include "biimpi.mm"
include "jcad.mm"
include "3ad2ant1.mm"
include "sylc.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "sylibr.mm"

theorem wwlknllvtx
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume wwlknllvtx.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( N WWalksN G ) -> ( ( W ` 0 ) e. V /\ ( W ` N ) e. V ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cc0
    cW
    cfv
    #
    cG
    cvtx
    cfv
    #
    wcel
    #
    cN
    cW
    cfv
    #
    @2
    wcel
    #
    wa
    #
    @1
    cV
    wcel
    #
    @4
    cV
    wcel
    #
    wa
    @0
    cN
    cn0
    wcel
    #
    cW
    @2
    cword
    wcel
    #
    cW
    chash
    cfv
    cN
    c1
    caddc
    co
    wceq
    #
    w3a
    vx
    cv
    #
    cW
    cfv
    #
    @2
    wcel
    #
    vx
    cc0
    cN
    cfz
    co
    #
    wral
    #
    @6
    cG
    cN
    cW
    wwlknbp1
    vx
    cG
    cN
    cW
    wwlknvtx
    @9
    @10
    @16
    @6
    wi
    @11
    @9
    @16
    @3
    @5
    @9
    @14
    @3
    vx
    cc0
    @15
    cN
    0elfz
    @12
    cc0
    wceq
    #
    @14
    @3
    wb
    @9
    @17
    @13
    @1
    @2
    @12
    cc0
    cW
    fveq2
    eleq1d
    adantl
    rspcdv
    @9
    @14
    @5
    vx
    cN
    @15
    @9
    cN
    @15
    wcel
    cN
    nn0fz0
    biimpi
    @12
    cN
    wceq
    #
    @14
    @5
    wb
    @9
    @18
    @13
    @4
    @2
    @12
    cN
    cW
    fveq2
    eleq1d
    adantl
    rspcdv
    jcad
    3ad2ant1
    sylc
    @7
    @3
    @8
    @5
    cV
    @2
    @1
    wwlknllvtx.v
    eleq2i
    cV
    @2
    @4
    wwlknllvtx.v
    eleq2i
    anbi12i
    sylibr
end
