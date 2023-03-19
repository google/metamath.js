include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "wnel.mm"
include "w3a.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cprod.mm"
include "cabs.mm"
include "cfv.mm"
include "cn.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "simp3.mm"
include "absprodnn.mm"
include "wceq.mm"
include "wb.mm"
include "breq2.mm"
include "ralbidv.mm"
include "adantl.mm"
include "absproddvds.mm"
include "rspcedvd.mm"

theorem fissn0dvds
  let vm: setvar m
  let vn: setvar n
  let cZ: class Z
  let vk: setvar k

  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint Z k
  disjoint k m
  disjoint k n
  assert |- ( ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) -> E. n e. NN A. m e. Z m || n )

  proof
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    cc0
    cZ
    wnel
    #
    w3a
    #
    vm
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    @4
    cZ
    vk
    cv
    vk
    cprod
    cabs
    cfv
    #
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    vn
    @8
    cn
    @3
    vk
    @8
    cZ
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @8
    eqid
    #
    @0
    @1
    @2
    simp3
    absprodnn
    @5
    @8
    wceq
    #
    @7
    @10
    wb
    @3
    @14
    @6
    @9
    vm
    cZ
    @5
    @8
    @4
    cdvds
    breq2
    ralbidv
    adantl
    @3
    vk
    @8
    vm
    cZ
    @11
    @12
    @13
    absproddvds
    rspcedvd
end
