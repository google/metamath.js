include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "clcmf.mm"
include "cfv.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "breq2.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com12.mm"
include "adantr.mm"
include "lcmfunsnlem.mm"
include "syl11.mm"
include "3impib.mm"

theorem lcmfdvds
  let vm: setvar m
  let cK: class K
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n

  disjoint K m
  disjoint Z m
  disjoint K k
  disjoint k m
  disjoint Z k
  disjoint Z n
  disjoint k n
  disjoint m n
  assert |- ( ( K e. ZZ /\ Z C_ ZZ /\ Z e. Fin ) -> ( A. m e. Z m || K -> ( _lcm ` Z ) || K ) )

  proof
    cK
    cz
    wcel
    #
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    vm
    cv
    #
    cK
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    cZ
    clcmf
    cfv
    #
    cK
    cdvds
    wbr
    #
    wi
    #
    @3
    vk
    cv
    #
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    @6
    @9
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    cZ
    vn
    cv
    #
    csn
    cun
    clcmf
    cfv
    @6
    @15
    clcm
    co
    wceq
    vn
    cz
    wral
    #
    wa
    @0
    @8
    @1
    @2
    wa
    @14
    @0
    @8
    wi
    @16
    @0
    @14
    @8
    @13
    @8
    vk
    cK
    cz
    @9
    cK
    wceq
    #
    @11
    @5
    @12
    @7
    @17
    @10
    @4
    vm
    cZ
    @9
    cK
    @3
    cdvds
    breq2
    ralbidv
    @9
    cK
    @6
    cdvds
    breq2
    imbi12d
    rspcv
    com12
    adantr
    vk
    vm
    vn
    cZ
    lcmfunsnlem
    syl11
    3impib
end
