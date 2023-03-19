include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "simp11.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "simp13.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp21.mm"
include "latmcl.mm"
include "simp22.mm"
include "simp23.mm"
include "catm.mm"
include "eqid.mm"
include "pmapmeet.mm"
include "cops.mm"
include "hlop.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "latmle2.mm"
include "simp3r.mm"
include "lattrd.mm"
include "pmapojoinN.mm"
include "syl31anc.mm"
include "simp3l.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3expia.mm"

theorem pl42lem1N
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pl42lem.b: |- B = ( Base ` K )
  assume pl42lem.l: |- .<_ = ( le ` K )
  assume pl42lem.j: |- .\/ = ( join ` K )
  assume pl42lem.m: |- ./\ = ( meet ` K )
  assume pl42lem.o: |- ._|_ = ( oc ` K )
  assume pl42lem.f: |- F = ( pmap ` K )
  assume pl42lem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B /\ V e. B ) ) -> ( ( X .<_ ( ._|_ ` Y ) /\ Z .<_ ( ._|_ ` W ) ) -> ( F ` ( ( ( ( X .\/ Y ) ./\ Z ) .\/ W ) ./\ V ) ) = ( ( ( ( ( F ` X ) .+ ( F ` Y ) ) i^i ( F ` Z ) ) .+ ( F ` W ) ) i^i ( F ` V ) ) ) )

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
    w3a
    #
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.pe
    cfv
    c.le
    wbr
    #
    cZ
    cW
    c.pe
    cfv
    #
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    c.or
    co
    #
    cZ
    c.an
    co
    #
    cW
    c.or
    co
    #
    cV
    c.an
    co
    cF
    cfv
    #
    cX
    cF
    cfv
    cY
    cF
    cfv
    c.pl
    co
    #
    cZ
    cF
    cfv
    #
    cin
    #
    cW
    cF
    cfv
    #
    c.pl
    co
    #
    cV
    cF
    cfv
    #
    cin
    #
    wceq
    @3
    @7
    @11
    w3a
    #
    @15
    @14
    cF
    cfv
    #
    @21
    cin
    #
    @22
    @23
    @0
    @14
    cB
    wcel
    #
    @6
    @15
    @25
    wceq
    @0
    @1
    @2
    @7
    @11
    simp11
    #
    @23
    cK
    clat
    wcel
    #
    @13
    cB
    wcel
    #
    @5
    @26
    @23
    @0
    @28
    @27
    cK
    hllat
    syl
    #
    @23
    @28
    @12
    cB
    wcel
    #
    @4
    @29
    @30
    @23
    @28
    @1
    @2
    @31
    @30
    @0
    @1
    @2
    @7
    @11
    simp12
    #
    @0
    @1
    @2
    @7
    @11
    simp13
    #
    cB
    c.or
    cK
    cX
    cY
    pl42lem.b
    pl42lem.j
    latjcl
    syl3anc
    #
    @3
    @4
    @5
    @6
    @11
    simp21
    #
    cB
    cK
    c.an
    @12
    cZ
    pl42lem.b
    pl42lem.m
    latmcl
    syl3anc
    #
    @3
    @4
    @5
    @6
    @11
    simp22
    #
    cB
    c.or
    cK
    @13
    cW
    pl42lem.b
    pl42lem.j
    latjcl
    syl3anc
    @3
    @4
    @5
    @6
    @11
    simp23
    cK
    catm
    cfv
    #
    cB
    cF
    cK
    c.an
    @14
    cV
    pl42lem.b
    pl42lem.m
    @38
    eqid
    #
    pl42lem.f
    pmapmeet
    syl3anc
    @23
    @24
    @20
    @21
    @23
    @24
    @13
    cF
    cfv
    #
    @19
    c.pl
    co
    #
    @20
    @23
    @0
    @29
    @5
    @13
    @9
    c.le
    wbr
    @24
    @41
    wceq
    @27
    @36
    @37
    @23
    cB
    cK
    c.le
    @13
    cZ
    @9
    pl42lem.b
    pl42lem.l
    @30
    @36
    @35
    @23
    cK
    cops
    wcel
    #
    @5
    @9
    cB
    wcel
    @23
    @0
    @42
    @27
    cK
    hlop
    syl
    @37
    cB
    cK
    c.pe
    cW
    pl42lem.b
    pl42lem.o
    opoccl
    syl2anc
    @23
    @28
    @31
    @4
    @13
    cZ
    c.le
    wbr
    @30
    @34
    @35
    cB
    cK
    c.le
    c.an
    @12
    cZ
    pl42lem.b
    pl42lem.l
    pl42lem.m
    latmle2
    syl3anc
    @3
    @7
    @8
    @10
    simp3r
    lattrd
    cB
    c.pl
    c.or
    cK
    c.le
    cF
    c.pe
    @13
    cW
    pl42lem.b
    pl42lem.l
    pl42lem.j
    pl42lem.f
    pl42lem.o
    pl42lem.p
    pmapojoinN
    syl31anc
    @23
    @40
    @18
    @19
    c.pl
    @23
    @40
    @12
    cF
    cfv
    #
    @17
    cin
    #
    @18
    @23
    @0
    @31
    @4
    @40
    @44
    wceq
    @27
    @34
    @35
    @38
    cB
    cF
    cK
    c.an
    @12
    cZ
    pl42lem.b
    pl42lem.m
    @39
    pl42lem.f
    pmapmeet
    syl3anc
    @23
    @43
    @16
    @17
    @23
    @0
    @1
    @2
    @8
    @43
    @16
    wceq
    @27
    @32
    @33
    @3
    @7
    @8
    @10
    simp3l
    cB
    c.pl
    c.or
    cK
    c.le
    cF
    c.pe
    cX
    cY
    pl42lem.b
    pl42lem.l
    pl42lem.j
    pl42lem.f
    pl42lem.o
    pl42lem.p
    pmapojoinN
    syl31anc
    ineq1d
    eqtrd
    oveq1d
    eqtrd
    ineq1d
    eqtrd
    3expia
end
