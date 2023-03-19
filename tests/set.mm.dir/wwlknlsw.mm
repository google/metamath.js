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
include "clsw.mm"
include "wwlknbp1.mm"
include "cmin.mm"
include "lsw.mm"
include "3ad2ant2.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqtr2d.mm"

theorem wwlknlsw
  let cG: class G
  let cN: class N
  let cW: class W


  assert |- ( W e. ( N WWalksN G ) -> ( W ` N ) = ( lastS ` W ) )

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
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cN
    cW
    cfv
    #
    cW
    clsw
    cfv
    #
    wceq
    cG
    cN
    cW
    wwlknbp1
    @6
    @8
    @3
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @7
    @2
    @0
    @8
    @10
    wceq
    @5
    cW
    @1
    lsw
    3ad2ant2
    @6
    @9
    cN
    cW
    @6
    @9
    @4
    c1
    cmin
    co
    #
    cN
    @5
    @0
    @9
    @11
    wceq
    @2
    @3
    @4
    c1
    cmin
    oveq1
    3ad2ant3
    @0
    @2
    @11
    cN
    wceq
    #
    @5
    @0
    cN
    cc
    wcel
    @12
    cN
    nn0cn
    cN
    pncan1
    syl
    3ad2ant1
    eqtrd
    fveq2d
    eqtr2d
    syl
end
