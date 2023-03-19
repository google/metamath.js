include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "cword.mm"
include "w3a.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cwwlks.mm"
include "crab.mm"
include "df-wwlksn.mm"
include "elmpt2cl.mm"
include "simpl.mm"
include "ancomd.mm"
include "wb.mm"
include "iswwlksn.mm"
include "adantr.mm"
include "wwlkbp.mm"
include "simprd.mm"
include "syl6bi.mm"
include "imp.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "mpancom.mm"

theorem wwlknbp
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  assume wwlkbp.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( N WWalksN G ) -> ( G e. _V /\ N e. NN0 /\ W e. Word V ) )

  proof
    cN
    cn0
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    #
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @1
    @0
    cW
    cV
    cword
    wcel
    #
    w3a
    #
    vn
    vg
    cn0
    cvv
    vw
    cv
    chash
    cfv
    vn
    cv
    c1
    caddc
    co
    wceq
    vw
    vg
    cv
    cwwlks
    cfv
    crab
    cN
    cG
    cwwlksn
    cW
    vw
    vg
    vn
    df-wwlksn
    elmpt2cl
    @2
    @3
    wa
    #
    @1
    @0
    wa
    @4
    @5
    @6
    @0
    @1
    @2
    @3
    simpl
    ancomd
    @2
    @3
    @4
    @2
    @3
    cW
    cG
    cwwlks
    cfv
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
    wa
    #
    @4
    @0
    @3
    @9
    wb
    @1
    cG
    cN
    cW
    iswwlksn
    adantr
    @7
    @4
    @8
    @7
    @1
    @4
    cG
    cV
    cW
    wwlkbp.v
    wwlkbp
    simprd
    adantr
    syl6bi
    imp
    @1
    @0
    @4
    df-3an
    sylanbrc
    mpancom
end
