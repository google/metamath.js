include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "catm.mm"
include "wss.mm"
include "simpl1.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "simpr3.mm"
include "latmcl.mm"
include "3jca.mm"
include "pmapjoin.mm"
include "ss2in.mm"
include "wceq.mm"
include "pmapmeet.mm"
include "sseqtr4d.mm"
include "jca.mm"
include "paddss12.mm"
include "sylc.mm"
include "sstrd.mm"

theorem pl42lem2N
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


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B /\ V e. B ) ) -> ( ( ( F ` X ) .+ ( F ` Y ) ) .+ ( ( ( F ` X ) .+ ( F ` W ) ) i^i ( ( F ` Y ) .+ ( F ` V ) ) ) ) C_ ( F ` ( ( X .\/ Y ) .\/ ( ( X .\/ W ) ./\ ( Y .\/ V ) ) ) ) )

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
    wa
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
    @9
    cW
    cF
    cfv
    c.pl
    co
    #
    @10
    cV
    cF
    cfv
    c.pl
    co
    #
    cin
    #
    c.pl
    co
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
    cW
    c.or
    co
    #
    cY
    cV
    c.or
    co
    #
    c.an
    co
    #
    cF
    cfv
    #
    c.pl
    co
    #
    @16
    @20
    c.or
    co
    cF
    cfv
    #
    @8
    @0
    @17
    cK
    catm
    cfv
    #
    wss
    #
    @21
    @24
    wss
    #
    w3a
    @11
    @17
    wss
    #
    @14
    @21
    wss
    #
    wa
    @15
    @22
    wss
    @8
    @0
    @25
    @26
    @0
    @1
    @2
    @7
    simpl1
    #
    @8
    @0
    @16
    cB
    wcel
    #
    @25
    @29
    @8
    cK
    clat
    wcel
    #
    @1
    @2
    @30
    @8
    @0
    @31
    @29
    cK
    hllat
    syl
    #
    @0
    @1
    @2
    @7
    simpl2
    #
    @0
    @1
    @2
    @7
    simpl3
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
    @24
    cB
    chlt
    cK
    cF
    @16
    pl42lem.b
    @24
    eqid
    #
    pl42lem.f
    pmapssat
    syl2anc
    @8
    @0
    @20
    cB
    wcel
    #
    @26
    @29
    @8
    @31
    @18
    cB
    wcel
    #
    @19
    cB
    wcel
    #
    @37
    @32
    @8
    @31
    @1
    @5
    @38
    @32
    @33
    @3
    @4
    @5
    @6
    simpr2
    #
    cB
    c.or
    cK
    cX
    cW
    pl42lem.b
    pl42lem.j
    latjcl
    syl3anc
    #
    @8
    @31
    @2
    @6
    @39
    @32
    @34
    @3
    @4
    @5
    @6
    simpr3
    #
    cB
    c.or
    cK
    cY
    cV
    pl42lem.b
    pl42lem.j
    latjcl
    syl3anc
    #
    cB
    cK
    c.an
    @18
    @19
    pl42lem.b
    pl42lem.m
    latmcl
    syl3anc
    #
    @24
    cB
    chlt
    cK
    cF
    @20
    pl42lem.b
    @36
    pl42lem.f
    pmapssat
    syl2anc
    3jca
    @8
    @27
    @28
    @8
    @31
    @1
    @2
    @27
    @32
    @33
    @34
    cB
    c.pl
    c.or
    cK
    cF
    cX
    cY
    pl42lem.b
    pl42lem.j
    pl42lem.f
    pl42lem.p
    pmapjoin
    syl3anc
    @8
    @14
    @18
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    cin
    #
    @21
    @8
    @12
    @45
    wss
    #
    @13
    @46
    wss
    #
    @14
    @47
    wss
    @8
    @31
    @1
    @5
    @48
    @32
    @33
    @40
    cB
    c.pl
    c.or
    cK
    cF
    cX
    cW
    pl42lem.b
    pl42lem.j
    pl42lem.f
    pl42lem.p
    pmapjoin
    syl3anc
    @8
    @31
    @2
    @6
    @49
    @32
    @34
    @42
    cB
    c.pl
    c.or
    cK
    cF
    cY
    cV
    pl42lem.b
    pl42lem.j
    pl42lem.f
    pl42lem.p
    pmapjoin
    syl3anc
    @12
    @45
    @13
    @46
    ss2in
    syl2anc
    @8
    @0
    @38
    @39
    @21
    @47
    wceq
    @29
    @41
    @43
    @24
    cB
    cF
    cK
    c.an
    @18
    @19
    pl42lem.b
    pl42lem.m
    @36
    pl42lem.f
    pmapmeet
    syl3anc
    sseqtr4d
    jca
    @24
    chlt
    c.pl
    cK
    @21
    @11
    @17
    @14
    @36
    pl42lem.p
    paddss12
    sylc
    @8
    @31
    @30
    @37
    @22
    @23
    wss
    @32
    @35
    @44
    cB
    c.pl
    c.or
    cK
    cF
    @16
    @20
    pl42lem.b
    pl42lem.j
    pl42lem.f
    pl42lem.p
    pmapjoin
    syl3anc
    sstrd
end
