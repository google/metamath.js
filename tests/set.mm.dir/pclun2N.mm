include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "co.mm"
include "catm.mm"
include "wss.mm"
include "wceq.mm"
include "simp1.mm"
include "eqid.mm"
include "psubssat.mm"
include "3adant3.mm"
include "3adant2.mm"
include "pclunN.mm"
include "syl3anc.mm"
include "paddclN.mm"
include "pclidN.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem pclun2N
  let c.pl: class .+
  let cS: class S
  let cU: class U
  let cK: class K
  let cX: class X
  let cY: class Y
  assume pclun2.s: |- S = ( PSubSp ` K )
  assume pclun2.p: |- .+ = ( +P ` K )
  assume pclun2.c: |- U = ( PCl ` K )


  assert |- ( ( K e. HL /\ X e. S /\ Y e. S ) -> ( U ` ( X u. Y ) ) = ( X .+ Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    w3a
    #
    cX
    cY
    cun
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
    @5
    @3
    @0
    cX
    cK
    catm
    cfv
    #
    wss
    #
    cY
    @7
    wss
    #
    @4
    @6
    wceq
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @8
    @2
    @7
    chlt
    cS
    cK
    cX
    @7
    eqid
    #
    pclun2.s
    psubssat
    3adant3
    @0
    @2
    @9
    @1
    @7
    chlt
    cS
    cK
    cY
    @11
    pclun2.s
    psubssat
    3adant2
    @7
    c.pl
    cU
    cK
    chlt
    cX
    cY
    @11
    pclun2.p
    pclun2.c
    pclunN
    syl3anc
    @3
    @0
    @5
    cS
    wcel
    @6
    @5
    wceq
    @10
    c.pl
    cS
    cK
    cX
    cY
    pclun2.s
    pclun2.p
    paddclN
    cS
    cU
    cK
    chlt
    @5
    pclun2.s
    pclun2.c
    pclidN
    syl2anc
    eqtrd
end
