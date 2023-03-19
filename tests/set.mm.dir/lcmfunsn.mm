include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "clcmf.mm"
include "cfv.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "lcmfunsnlem.mm"
include "sneq.mm"
include "uneq2d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "com12.mm"
include "adantl.mm"
include "syl.mm"
include "3impia.mm"

theorem lcmfunsn
  let cN: class N
  let cY: class Y
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m


  assert |- ( ( Y C_ ZZ /\ Y e. Fin /\ N e. ZZ ) -> ( _lcm ` ( Y u. { N } ) ) = ( ( _lcm ` Y ) lcm N ) )

  proof
    cY
    cz
    wss
    #
    cY
    cfn
    wcel
    #
    cN
    cz
    wcel
    #
    cY
    cN
    csn
    #
    cun
    #
    clcmf
    cfv
    #
    cY
    clcmf
    cfv
    #
    cN
    clcm
    co
    #
    wceq
    #
    @0
    @1
    wa
    vm
    cv
    vk
    cv
    #
    cdvds
    wbr
    vm
    cY
    wral
    @6
    @9
    cdvds
    wbr
    wi
    vk
    cz
    wral
    #
    cY
    vn
    cv
    #
    csn
    #
    cun
    #
    clcmf
    cfv
    #
    @6
    @11
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    @2
    @8
    wi
    #
    vk
    vm
    vn
    cY
    lcmfunsnlem
    @17
    @18
    @10
    @2
    @17
    @8
    @16
    @8
    vn
    cN
    cz
    @11
    cN
    wceq
    #
    @14
    @5
    @15
    @7
    @19
    @13
    @4
    clcmf
    @19
    @12
    @3
    cY
    @11
    cN
    sneq
    uneq2d
    fveq2d
    @11
    cN
    @6
    clcm
    oveq2
    eqeq12d
    rspcv
    com12
    adantl
    syl
    3impia
end
