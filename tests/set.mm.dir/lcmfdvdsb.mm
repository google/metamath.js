include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "clcmf.mm"
include "cfv.mm"
include "lcmfdvds.mm"
include "wa.mm"
include "wi.mm"
include "dvdslcmf.mm"
include "breq1.mm"
include "rspcv.mm"
include "ssel.mm"
include "adantr.mm"
include "com12.mm"
include "imp.mm"
include "lcmfcl.mm"
include "nn0zd.mm"
include "adantl.mm"
include "simplr.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "expd.mm"
include "exp31.mm"
include "com23.mm"
include "com24.mm"
include "com45.mm"
include "syld.mm"
include "com15.mm"
include "mpd.mm"
include "3impib.mm"
include "imp31.mm"
include "ralrimiva.mm"
include "ex.mm"
include "impbid.mm"

theorem lcmfdvdsb
  let vm: setvar m
  let cK: class K
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x

  disjoint K m
  disjoint Z m
  disjoint K k
  disjoint k m
  disjoint Z k
  disjoint Z n
  disjoint k n
  disjoint m n
  disjoint Z x
  disjoint m x
  assert |- ( ( K e. ZZ /\ Z C_ ZZ /\ Z e. Fin ) -> ( A. m e. Z m || K <-> ( _lcm ` Z ) || K ) )

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
    w3a
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
    vm
    cK
    cZ
    lcmfdvds
    @3
    @8
    @6
    @3
    @8
    wa
    @5
    vm
    cZ
    @3
    @8
    @4
    cZ
    wcel
    #
    @5
    @0
    @1
    @2
    @8
    @9
    @5
    wi
    wi
    #
    @1
    @2
    wa
    #
    @0
    @10
    @11
    vx
    cv
    #
    @7
    cdvds
    wbr
    #
    vx
    cZ
    wral
    #
    @0
    @10
    wi
    vx
    cZ
    dvdslcmf
    @9
    @14
    @0
    @8
    @11
    @5
    @9
    @14
    @4
    @7
    cdvds
    wbr
    #
    @0
    @8
    @11
    @5
    wi
    wi
    wi
    @13
    @15
    vx
    @4
    cZ
    @12
    @4
    @7
    cdvds
    breq1
    rspcv
    @9
    @15
    @0
    @11
    @8
    @5
    @9
    @11
    @0
    @15
    @8
    @5
    wi
    #
    @9
    @0
    @11
    @15
    @16
    wi
    #
    @9
    @0
    @11
    @17
    @9
    @0
    wa
    #
    @11
    wa
    #
    @15
    @8
    @5
    @19
    @4
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @0
    @15
    @8
    wa
    @5
    wi
    @18
    @11
    @20
    @9
    @11
    @20
    wi
    @0
    @11
    @9
    @20
    @1
    @9
    @20
    wi
    @2
    cZ
    cz
    @4
    ssel
    adantr
    com12
    adantr
    imp
    @11
    @21
    @18
    @11
    @7
    cZ
    lcmfcl
    nn0zd
    adantl
    @9
    @0
    @11
    simplr
    @4
    @7
    cK
    dvdstr
    syl3anc
    expd
    exp31
    com23
    com24
    com45
    syld
    com15
    mpd
    com12
    3impib
    imp31
    ralrimiva
    ex
    impbid
end
