include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cpfx.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "cmin.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "eqcomd.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "c0.mm"
include "wne.mm"
include "simp2.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "nn0p1gt0.mm"
include "wb.mm"
include "breq2.mm"
include "mpbird.mm"
include "hashneq0.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "pfxlswccat.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "ex.mm"

theorem ccats1pfxeq
  let cU: class U
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ U e. Word V /\ ( # ` U ) = ( ( # ` W ) + 1 ) ) -> ( W = ( U prefix ( # ` W ) ) -> U = ( W ++ <" ( lastS ` U ) "> ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cU
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cW
    cU
    @4
    cpfx
    co
    #
    wceq
    #
    cU
    cW
    cU
    clsw
    cfv
    cs1
    #
    cconcat
    co
    #
    wceq
    @7
    @9
    wa
    @11
    @8
    @10
    cconcat
    co
    #
    cU
    @9
    @11
    @12
    wceq
    @7
    cW
    @8
    @10
    cconcat
    oveq1
    adantl
    @7
    @12
    cU
    wceq
    @9
    @7
    @12
    cU
    @3
    c1
    cmin
    co
    #
    cpfx
    co
    #
    @10
    cconcat
    co
    #
    cU
    @7
    @8
    @14
    @10
    cconcat
    @7
    @4
    @13
    cU
    cpfx
    @7
    @4
    @5
    c1
    cmin
    co
    #
    @13
    @1
    @2
    @4
    @16
    wceq
    @6
    @1
    @16
    @4
    @1
    @4
    cc
    wcel
    @16
    @4
    wceq
    @1
    @4
    cV
    cW
    lencl
    #
    nn0cnd
    @4
    pncan1
    syl
    eqcomd
    3ad2ant1
    @6
    @1
    @16
    @13
    wceq
    @2
    @6
    @13
    @16
    @3
    @5
    c1
    cmin
    oveq1
    eqcomd
    3ad2ant3
    eqtrd
    oveq2d
    oveq1d
    @7
    @2
    cU
    c0
    wne
    #
    @15
    cU
    wceq
    @1
    @2
    @6
    simp2
    @7
    cc0
    @3
    clt
    wbr
    #
    @18
    @7
    @19
    cc0
    @5
    clt
    wbr
    #
    @1
    @2
    @20
    @6
    @1
    @4
    cn0
    wcel
    @20
    @17
    @4
    nn0p1gt0
    syl
    3ad2ant1
    @6
    @1
    @19
    @20
    wb
    @2
    @3
    @5
    cc0
    clt
    breq2
    3ad2ant3
    mpbird
    @2
    @1
    @19
    @18
    wb
    @6
    cU
    @0
    hashneq0
    3ad2ant2
    mpbid
    cV
    cU
    pfxlswccat
    syl2anc
    eqtrd
    adantr
    eqtr2d
    ex
end
