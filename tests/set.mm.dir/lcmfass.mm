include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "clcmf.mm"
include "cfv.mm"
include "csn.mm"
include "clcm.mm"
include "co.mm"
include "cun.mm"
include "cabs.mm"
include "wceq.mm"
include "lcmfcl.mm"
include "nn0zd.mm"
include "lcmfsn.mm"
include "syl.mm"
include "cn0.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "absid.mm"
include "3syl.mm"
include "eqtrd.mm"
include "eqtr2d.mm"
include "oveqan12d.mm"
include "snssd.mm"
include "snfi.mm"
include "jctir.mm"
include "lcmfun.mm"
include "sylan.mm"
include "sylan2.mm"
include "3eqtr4d.mm"

theorem lcmfass
  let cY: class Y
  let cZ: class Z


  assert |- ( ( ( Y C_ ZZ /\ Y e. Fin ) /\ ( Z C_ ZZ /\ Z e. Fin ) ) -> ( _lcm ` ( { ( _lcm ` Y ) } u. Z ) ) = ( _lcm ` ( Y u. { ( _lcm ` Z ) } ) ) )

  proof
    cY
    cz
    wss
    cY
    cfn
    wcel
    wa
    #
    cZ
    cz
    wss
    cZ
    cfn
    wcel
    wa
    #
    wa
    cY
    clcmf
    cfv
    #
    csn
    #
    clcmf
    cfv
    #
    cZ
    clcmf
    cfv
    #
    clcm
    co
    #
    @2
    @5
    csn
    #
    clcmf
    cfv
    #
    clcm
    co
    #
    @3
    cZ
    cun
    clcmf
    cfv
    #
    cY
    @7
    cun
    clcmf
    cfv
    #
    @0
    @1
    @4
    @2
    @5
    @8
    clcm
    @0
    @4
    @2
    cabs
    cfv
    #
    @2
    @0
    @2
    cz
    wcel
    @4
    @12
    wceq
    @0
    @2
    cY
    lcmfcl
    #
    nn0zd
    #
    @2
    lcmfsn
    syl
    @0
    @2
    cn0
    wcel
    #
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @12
    @2
    wceq
    @13
    @15
    @16
    @17
    @2
    nn0re
    @2
    nn0ge0
    jca
    @2
    absid
    3syl
    eqtrd
    @1
    @8
    @5
    cabs
    cfv
    #
    @5
    @1
    @5
    cz
    wcel
    @8
    @18
    wceq
    @1
    @5
    cZ
    lcmfcl
    #
    nn0zd
    #
    @5
    lcmfsn
    syl
    @1
    @5
    cn0
    wcel
    #
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    @18
    @5
    wceq
    @19
    @21
    @22
    @23
    @5
    nn0re
    @5
    nn0ge0
    jca
    @5
    absid
    3syl
    eqtr2d
    oveqan12d
    @0
    @3
    cz
    wss
    #
    @3
    cfn
    wcel
    #
    wa
    @1
    @10
    @6
    wceq
    @0
    @24
    @25
    @0
    @2
    cz
    @14
    snssd
    @2
    snfi
    jctir
    @3
    cZ
    lcmfun
    sylan
    @1
    @0
    @7
    cz
    wss
    #
    @7
    cfn
    wcel
    #
    wa
    @11
    @9
    wceq
    @1
    @26
    @27
    @1
    @5
    cz
    @20
    snssd
    @5
    snfi
    jctir
    cY
    @7
    lcmfun
    sylan2
    3eqtr4d
end
