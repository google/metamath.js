include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp22.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp23.mm"
include "latmcl.mm"
include "wss.mm"
include "cin.mm"
include "catm.mm"
include "cpsubsp.mm"
include "simp1.mm"
include "eqid.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "pmapsub.mm"
include "simp3l.mm"
include "wb.mm"
include "pmaple.mm"
include "mpbid.mm"
include "pmod1i.mm"
include "3impia.mm"
include "syl131anc.mm"
include "pmapmeet.mm"
include "simp3r.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "pmapjoin.mm"
include "eqsstrd.mm"
include "mpbird.mm"
include "mod1ile.mm"
include "latasymd.mm"
include "3expia.mm"

theorem hlmod1i
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hlmod.b: |- B = ( Base ` K )
  assume hlmod.l: |- .<_ = ( le ` K )
  assume hlmod.j: |- .\/ = ( join ` K )
  assume hlmod.m: |- ./\ = ( meet ` K )
  assume hlmod.f: |- F = ( pmap ` K )
  assume hlmod.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .<_ Z /\ ( F ` ( X .\/ Y ) ) = ( ( F ` X ) .+ ( F ` Y ) ) ) -> ( ( X .\/ Y ) ./\ Z ) = ( X .\/ ( Y ./\ Z ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cZ
    c.le
    wbr
    #
    cX
    cY
    c.or
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wa
    #
    @6
    cZ
    c.an
    co
    #
    cX
    cY
    cZ
    c.an
    co
    #
    c.or
    co
    #
    wceq
    @0
    @4
    @12
    w3a
    #
    cB
    cK
    c.le
    @13
    @15
    hlmod.b
    hlmod.l
    @0
    @4
    cK
    clat
    wcel
    #
    @12
    cK
    hllat
    3ad2ant1
    #
    @16
    @17
    @6
    cB
    wcel
    #
    @3
    @13
    cB
    wcel
    #
    @18
    @16
    @17
    @1
    @2
    @19
    @18
    @0
    @1
    @2
    @3
    @12
    simp21
    #
    @0
    @1
    @2
    @3
    @12
    simp22
    #
    cB
    c.or
    cK
    cX
    cY
    hlmod.b
    hlmod.j
    latjcl
    syl3anc
    #
    @0
    @1
    @2
    @3
    @12
    simp23
    #
    cB
    cK
    c.an
    @6
    cZ
    hlmod.b
    hlmod.m
    latmcl
    syl3anc
    #
    @16
    @17
    @1
    @14
    cB
    wcel
    #
    @15
    cB
    wcel
    #
    @18
    @21
    @16
    @17
    @2
    @3
    @26
    @18
    @22
    @24
    cB
    cK
    c.an
    cY
    cZ
    hlmod.b
    hlmod.m
    latmcl
    syl3anc
    #
    cB
    c.or
    cK
    cX
    @14
    hlmod.b
    hlmod.j
    latjcl
    syl3anc
    #
    @16
    @13
    @15
    c.le
    wbr
    #
    @13
    cF
    cfv
    #
    @15
    cF
    cfv
    #
    wss
    #
    @16
    @31
    @8
    @14
    cF
    cfv
    #
    c.pl
    co
    #
    @32
    @16
    @10
    cZ
    cF
    cfv
    #
    cin
    #
    @8
    @9
    @36
    cin
    #
    c.pl
    co
    #
    @31
    @35
    @16
    @0
    @8
    cK
    catm
    cfv
    #
    wss
    #
    @9
    @40
    wss
    #
    @36
    cK
    cpsubsp
    cfv
    #
    wcel
    #
    @8
    @36
    wss
    #
    @37
    @39
    wceq
    #
    @0
    @4
    @12
    simp1
    #
    @16
    @0
    @1
    @41
    @47
    @21
    @40
    cB
    chlt
    cK
    cF
    cX
    hlmod.b
    @40
    eqid
    #
    hlmod.f
    pmapssat
    syl2anc
    @16
    @0
    @2
    @42
    @47
    @22
    @40
    cB
    chlt
    cK
    cF
    cY
    hlmod.b
    @48
    hlmod.f
    pmapssat
    syl2anc
    @16
    @17
    @3
    @44
    @18
    @24
    cB
    @43
    cK
    cF
    cZ
    hlmod.b
    @43
    eqid
    #
    hlmod.f
    pmapsub
    syl2anc
    @16
    @5
    @45
    @0
    @4
    @5
    @11
    simp3l
    #
    @16
    @0
    @1
    @3
    @5
    @45
    wb
    @47
    @21
    @24
    cB
    cK
    c.le
    cF
    cX
    cZ
    hlmod.b
    hlmod.l
    hlmod.f
    pmaple
    syl3anc
    mpbid
    @0
    @41
    @42
    @44
    w3a
    @45
    @46
    @40
    c.pl
    @43
    cK
    @8
    @9
    @36
    @48
    @49
    hlmod.p
    pmod1i
    3impia
    syl131anc
    @16
    @31
    @7
    @36
    cin
    #
    @37
    @16
    @0
    @19
    @3
    @31
    @51
    wceq
    @47
    @23
    @24
    @40
    cB
    cF
    cK
    c.an
    @6
    cZ
    hlmod.b
    hlmod.m
    @48
    hlmod.f
    pmapmeet
    syl3anc
    @16
    @7
    @10
    @36
    @0
    @4
    @5
    @11
    simp3r
    ineq1d
    eqtrd
    @16
    @34
    @38
    @8
    c.pl
    @16
    @0
    @2
    @3
    @34
    @38
    wceq
    @47
    @22
    @24
    @40
    cB
    cF
    cK
    c.an
    cY
    cZ
    hlmod.b
    hlmod.m
    @48
    hlmod.f
    pmapmeet
    syl3anc
    oveq2d
    3eqtr4d
    @16
    @17
    @1
    @26
    @35
    @32
    wss
    @18
    @21
    @28
    cB
    c.pl
    c.or
    cK
    cF
    cX
    @14
    hlmod.b
    hlmod.j
    hlmod.f
    hlmod.p
    pmapjoin
    syl3anc
    eqsstrd
    @16
    @0
    @20
    @27
    @30
    @33
    wb
    @47
    @25
    @29
    cB
    cK
    c.le
    cF
    @13
    @15
    hlmod.b
    hlmod.l
    hlmod.f
    pmaple
    syl3anc
    mpbird
    @16
    @17
    @1
    @2
    @3
    @5
    @15
    @13
    c.le
    wbr
    #
    @18
    @21
    @22
    @24
    @50
    @17
    @4
    @5
    @52
    cB
    c.or
    cK
    c.le
    c.an
    cX
    cY
    cZ
    hlmod.b
    hlmod.l
    hlmod.j
    hlmod.m
    mod1ile
    3impia
    syl131anc
    latasymd
    3expia
end
