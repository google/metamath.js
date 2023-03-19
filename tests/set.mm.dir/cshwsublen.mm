include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "wi.mm"
include "cc0.mm"
include "oveq2.mm"
include "zcn.mm"
include "subid1d.mm"
include "adantl.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "ex.mm"
include "wne.mm"
include "cmo.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "cn0.mm"
include "lencl.mm"
include "cn.mm"
include "elnnne0.mm"
include "nnrp.mm"
include "sylbir.mm"
include "syl.mm"
include "adantr.mm"
include "impcom.mm"
include "jca.mm"
include "modeqmodmin.mm"
include "cshwmodn.mm"
include "simpl.mm"
include "nn0zd.mm"
include "zsubcl.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3eqtr4d.mm"
include "pm2.61ine.mm"

theorem cshwsublen
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( W cyclShift N ) = ( W cyclShift ( N - ( # ` W ) ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    cW
    cN
    cW
    chash
    cfv
    #
    cmin
    co
    #
    ccsh
    co
    #
    wceq
    #
    wi
    @4
    cc0
    @4
    cc0
    wceq
    #
    @2
    @7
    @8
    @2
    wa
    #
    cN
    @5
    cW
    ccsh
    @9
    @5
    cN
    @8
    @2
    @5
    cN
    cc0
    cmin
    co
    #
    cN
    @4
    cc0
    cN
    cmin
    oveq2
    @1
    @10
    cN
    wceq
    @0
    @1
    cN
    cN
    zcn
    subid1d
    adantl
    sylan9eq
    eqcomd
    oveq2d
    ex
    @4
    cc0
    wne
    #
    @2
    @7
    @11
    @2
    wa
    #
    cW
    cN
    @4
    cmo
    co
    #
    ccsh
    co
    #
    cW
    @5
    @4
    cmo
    co
    #
    ccsh
    co
    #
    @3
    @6
    @12
    @13
    @15
    cW
    ccsh
    @12
    cN
    cr
    wcel
    #
    @4
    crp
    wcel
    #
    wa
    @13
    @15
    wceq
    @12
    @17
    @18
    @2
    @17
    @11
    @1
    @17
    @0
    cN
    zre
    adantl
    adantl
    @2
    @11
    @18
    @0
    @11
    @18
    wi
    #
    @1
    @0
    @4
    cn0
    wcel
    #
    @19
    cV
    cW
    lencl
    #
    @20
    @11
    @18
    @20
    @11
    wa
    @4
    cn
    wcel
    @18
    @4
    elnnne0
    @4
    nnrp
    sylbir
    ex
    syl
    adantr
    impcom
    jca
    cN
    @4
    modeqmodmin
    syl
    oveq2d
    @2
    @3
    @14
    wceq
    @11
    cN
    cV
    cW
    cshwmodn
    adantl
    @12
    @0
    @5
    cz
    wcel
    #
    wa
    #
    @6
    @16
    wceq
    @2
    @23
    @11
    @2
    @0
    @22
    @0
    @1
    simpl
    @1
    @0
    @22
    @0
    @1
    @4
    cz
    wcel
    @22
    @0
    @4
    @21
    nn0zd
    cN
    @4
    zsubcl
    sylan2
    ancoms
    jca
    adantl
    @5
    cV
    cW
    cshwmodn
    syl
    3eqtr4d
    ex
    pm2.61ine
end
