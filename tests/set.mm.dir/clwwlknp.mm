include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "clwwlknbp.mm"
include "simpr.mm"
include "cn.mm"
include "clwwlknnn.mm"
include "isclwwlknx.mm"
include "3simpc.mm"
include "adantr.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "anbi1d.mm"
include "ad2antll.mm"
include "mpbid.mm"
include "jca.mm"
include "mpdan.mm"
include "3anass.mm"
include "sylibr.mm"

theorem clwwlknp
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume isclwwlknx.v: |- V = ( Vtx ` G )
  assume isclwwlknx.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  disjoint N i
  assert |- ( W e. ( N ClWWalksN G ) -> ( ( W e. Word V /\ ( # ` W ) = N ) /\ A. i e. ( 0 ..^ ( N - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vi
    cv
    #
    cW
    cfv
    @5
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    #
    vi
    cc0
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cW
    clsw
    cfv
    cc0
    cW
    cfv
    cpr
    cE
    wcel
    #
    wa
    #
    wa
    #
    @4
    @9
    @10
    w3a
    @0
    @4
    @12
    cG
    cN
    cV
    cW
    isclwwlknx.v
    clwwlknbp
    @0
    @4
    wa
    #
    @4
    @11
    @0
    @4
    simpr
    @13
    @6
    vi
    cc0
    @2
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @10
    wa
    #
    @11
    @0
    @17
    @4
    cN
    cn
    wcel
    #
    @0
    @17
    cG
    cN
    cW
    clwwlknnn
    @18
    @0
    @1
    @16
    @10
    w3a
    #
    @3
    wa
    @17
    vi
    cE
    cG
    cN
    cV
    cW
    isclwwlknx.v
    isclwwlknx.e
    isclwwlknx
    @19
    @17
    @3
    @1
    @16
    @10
    3simpc
    adantr
    syl6bi
    mpcom
    adantr
    @3
    @17
    @11
    wb
    @0
    @1
    @3
    @16
    @9
    @10
    @3
    @6
    vi
    @15
    @8
    @3
    @14
    @7
    cc0
    cfzo
    @2
    cN
    c1
    cmin
    oveq1
    oveq2d
    raleqdv
    anbi1d
    ad2antll
    mpbid
    jca
    mpdan
    @4
    @9
    @10
    3anass
    sylibr
end
