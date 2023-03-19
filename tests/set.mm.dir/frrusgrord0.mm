include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wa.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "cfusgr.mm"
include "wi.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "anim1i.mm"
include "isfusgr.mm"
include "sylibr.mm"
include "fusgreghash2wsp.mm"
include "stoic3.mm"
include "imp.mm"
include "wb.mm"
include "frgrhash2wsp.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "3adant3.mm"
include "adantr.mm"
include "cc.mm"
include "cc0.mm"
include "frrusgrord0lem.mm"
include "peano2cnm.mm"
include "3ad2ant2.mm"
include "kcnktkm1cn.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "mulcand.mm"
include "npcan1.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "ex.mm"
include "sylbid.mm"
include "syl.mm"
include "sylbird.mm"
include "mpd.mm"

theorem frrusgrord0
  let vv: setvar v
  let cG: class G
  let cK: class K
  let cV: class V
  assume frrusgrord0.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint K v
  disjoint V v
  assert |- ( ( G e. FriendGraph /\ V e. Fin /\ V =/= (/) ) -> ( A. v e. V ( ( VtxDeg ` G ) ` v ) = K -> ( # ` V ) = ( ( K x. ( K - 1 ) ) + 1 ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cV
    c0
    wne
    #
    w3a
    #
    vv
    cv
    cG
    cvtxdg
    cfv
    cfv
    cK
    wceq
    vv
    cV
    wral
    #
    cV
    chash
    cfv
    #
    cK
    cK
    c1
    cmin
    co
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    @3
    @4
    wa
    #
    c2
    cG
    cwwspthsn
    co
    chash
    cfv
    #
    @5
    @6
    cmul
    co
    #
    wceq
    #
    @8
    @3
    @4
    @12
    @0
    @1
    cG
    cfusgr
    wcel
    #
    @2
    @4
    @12
    wi
    @0
    @1
    wa
    #
    cG
    cusgr
    wcel
    #
    @1
    wa
    @13
    @0
    @15
    @1
    cG
    frgrusgr
    anim1i
    cG
    cV
    frrusgrord0.v
    isfusgr
    sylibr
    vv
    cG
    cK
    cV
    frrusgrord0.v
    fusgreghash2wsp
    stoic3
    imp
    @9
    @12
    @5
    @5
    c1
    cmin
    co
    #
    cmul
    co
    #
    @11
    wceq
    #
    @8
    @3
    @18
    @12
    wb
    #
    @4
    @0
    @1
    @19
    @2
    @14
    @17
    @10
    @11
    @14
    @10
    @17
    cG
    cV
    frrusgrord0.v
    frgrhash2wsp
    eqcomd
    eqeq1d
    3adant3
    adantr
    @9
    cK
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    w3a
    #
    @18
    @8
    wi
    vv
    cG
    cK
    cV
    frrusgrord0.v
    frrusgrord0lem
    @23
    @18
    @16
    @6
    wceq
    #
    @8
    @23
    @16
    @6
    @5
    @21
    @20
    @16
    cc
    wcel
    @22
    @5
    peano2cnm
    3ad2ant2
    @20
    @21
    @6
    cc
    wcel
    @22
    cK
    kcnktkm1cn
    3ad2ant1
    @20
    @21
    @22
    simp2
    @20
    @21
    @22
    simp3
    mulcand
    @21
    @20
    @24
    @8
    wi
    @22
    @21
    @24
    @8
    @21
    @24
    @5
    @16
    c1
    caddc
    co
    @7
    @5
    npcan1
    @16
    @6
    c1
    caddc
    oveq1
    sylan9req
    ex
    3ad2ant2
    sylbid
    syl
    sylbird
    mpd
    ex
end
