include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "w3a.mm"
include "cwwlksn.mm"
include "co.mm"
include "cwwlks.mm"
include "eqid.mm"
include "wwlknbp.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "iswwlksn.mm"
include "3ad2ant2.mm"
include "simpl.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem wwlkswwlksn
  let cG: class G
  let cN: class N
  let cW: class W


  assert |- ( W e. ( N WWalksN G ) -> W e. ( WWalks ` G ) )

  proof
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    w3a
    #
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cW
    cG
    cwwlks
    cfv
    wcel
    #
    cG
    cN
    @2
    cW
    @2
    eqid
    wwlknbp
    @4
    @5
    @6
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
    @6
    @1
    @0
    @5
    @8
    wb
    @3
    cG
    cN
    cW
    iswwlksn
    3ad2ant2
    @6
    @7
    simpl
    syl6bi
    mpcom
end
