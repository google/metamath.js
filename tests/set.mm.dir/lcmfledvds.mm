include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "wnel.mm"
include "w3a.mm"
include "cn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "clcmf.mm"
include "cfv.mm"
include "cle.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "lcmfn0val.mm"
include "adantr.mm"
include "c1.mm"
include "cuz.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "simpr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylibr.mm"
include "infssuzle.mm"
include "sylancr.mm"
include "3ad2antl1.mm"
include "eqbrtrd.mm"
include "ex.mm"

theorem lcmfledvds
  let vm: setvar m
  let cK: class K
  let cZ: class Z
  let vk: setvar k

  disjoint K m
  disjoint Z m
  disjoint K k
  disjoint k m
  disjoint Z k
  assert |- ( ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) -> ( ( K e. NN /\ A. m e. Z m || K ) -> ( _lcm ` Z ) <_ K ) )

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
    cK
    cn
    wcel
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
    wa
    #
    cZ
    clcmf
    cfv
    #
    cK
    cle
    wbr
    @3
    @7
    wa
    @8
    @4
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
    vk
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cK
    cle
    @3
    @8
    @13
    wceq
    @7
    vm
    vk
    cZ
    lcmfn0val
    adantr
    @0
    @1
    @7
    @13
    cK
    cle
    wbr
    #
    @2
    @0
    @7
    wa
    #
    @12
    c1
    cuz
    cfv
    #
    wss
    cK
    @12
    wcel
    #
    @14
    @12
    cn
    @16
    @11
    vk
    cn
    ssrab2
    nnuz
    sseqtri
    @15
    @7
    @17
    @0
    @7
    simpr
    @11
    @6
    vk
    cK
    cn
    @9
    cK
    wceq
    @10
    @5
    vm
    cZ
    @9
    cK
    @4
    cdvds
    breq2
    ralbidv
    elrab
    sylibr
    cK
    @12
    c1
    infssuzle
    sylancr
    3ad2antl1
    eqbrtrd
    ex
end
