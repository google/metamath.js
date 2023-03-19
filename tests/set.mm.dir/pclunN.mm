include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "co.mm"
include "simp1.mm"
include "paddunssN.mm"
include "paddssat.mm"
include "pclssN.mm"
include "syl3anc.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "3adant1.mm"
include "pclssidN.mm"
include "syl2anc.mm"
include "sylibr.mm"
include "cpsubsp.mm"
include "wb.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "pclclN.mm"
include "paddss.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "psubssat.mm"
include "wceq.mm"
include "pclidN.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem pclunN
  let cA: class A
  let c.pl: class .+
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  assume pclun.a: |- A = ( Atoms ` K )
  assume pclun.p: |- .+ = ( +P ` K )
  assume pclun.c: |- U = ( PCl ` K )


  assert |- ( ( K e. V /\ X C_ A /\ Y C_ A ) -> ( U ` ( X u. Y ) ) = ( U ` ( X .+ Y ) ) )

  proof
    cK
    cV
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cX
    cY
    cun
    #
    cU
    cfv
    #
    cX
    cY
    c.pl
    co
    #
    cU
    cfv
    #
    @3
    @0
    @4
    @6
    wss
    @6
    cA
    wss
    @5
    @7
    wss
    @0
    @1
    @2
    simp1
    #
    cA
    cV
    c.pl
    cK
    cX
    cY
    pclun.a
    pclun.p
    paddunssN
    cA
    cV
    c.pl
    cK
    cX
    cY
    pclun.a
    pclun.p
    paddssat
    cA
    cU
    cK
    cV
    @4
    @6
    pclun.a
    pclun.c
    pclssN
    syl3anc
    @3
    @7
    @5
    cU
    cfv
    #
    @5
    @3
    @0
    @6
    @5
    wss
    #
    @5
    cA
    wss
    #
    @7
    @9
    wss
    @8
    @3
    cX
    @5
    wss
    cY
    @5
    wss
    wa
    #
    @10
    @3
    @4
    @5
    wss
    #
    @12
    @3
    @0
    @4
    cA
    wss
    #
    @13
    @8
    @1
    @2
    @14
    @0
    @1
    @2
    wa
    @14
    cX
    cY
    cA
    unss
    biimpi
    3adant1
    #
    cA
    cU
    cK
    cV
    @4
    pclun.a
    pclun.c
    pclssidN
    syl2anc
    cX
    cY
    @5
    unss
    sylibr
    @3
    @0
    @1
    @2
    @5
    cK
    cpsubsp
    cfv
    #
    wcel
    #
    @12
    @10
    wb
    @8
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    @0
    @14
    @17
    @8
    @15
    cA
    @16
    cU
    cK
    cV
    @4
    pclun.a
    @16
    eqid
    #
    pclun.c
    pclclN
    syl2anc
    #
    cA
    cV
    c.pl
    @16
    cK
    cX
    cY
    @5
    pclun.a
    @18
    pclun.p
    paddss
    syl13anc
    mpbid
    @3
    @0
    @17
    @11
    @8
    @19
    cA
    cV
    @16
    cK
    @5
    pclun.a
    @18
    psubssat
    syl2anc
    cA
    cU
    cK
    cV
    @6
    @5
    pclun.a
    pclun.c
    pclssN
    syl3anc
    @3
    @0
    @17
    @9
    @5
    wceq
    @8
    @19
    @16
    cU
    cK
    cV
    @5
    @18
    pclun.c
    pclidN
    syl2anc
    sseqtrd
    eqssd
end
