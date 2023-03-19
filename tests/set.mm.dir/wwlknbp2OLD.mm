include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "wwlknbp1.mm"
include "3simpc.mm"
include "syl.mm"

theorem wwlknbp2OLD
  let cG: class G
  let cN: class N
  let cW: class W


  assert |- ( W e. ( N WWalksN G ) -> ( W e. Word ( Vtx ` G ) /\ ( # ` W ) = ( N + 1 ) ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    cN
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
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
    @1
    @2
    wa
    cG
    cN
    cW
    wwlknbp1
    @0
    @1
    @2
    3simpc
    syl
end
