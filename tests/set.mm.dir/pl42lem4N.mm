include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "pl42lem1N.mm"
include "3impia.mm"
include "pl42lem3N.mm"
include "cpsubsp.mm"
include "simpl1.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "eqid.mm"
include "pmapsub.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "simpr2.mm"
include "simpr3.mm"
include "pmodl42N.mm"
include "syl32anc.mm"
include "pl42lem2N.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "3adant3.mm"
include "3expia.mm"

theorem pl42lem4N
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


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B /\ V e. B ) ) -> ( ( X .<_ ( ._|_ ` Y ) /\ Z .<_ ( ._|_ ` W ) ) -> ( F ` ( ( ( ( X .\/ Y ) ./\ Z ) .\/ W ) ./\ V ) ) C_ ( F ` ( ( X .\/ Y ) .\/ ( ( X .\/ W ) ./\ ( Y .\/ V ) ) ) ) ) )

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
    cZ
    cW
    c.pe
    cfv
    c.le
    wbr
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
    cW
    c.or
    co
    cV
    c.an
    co
    cF
    cfv
    #
    @9
    cX
    cW
    c.or
    co
    cY
    cV
    c.or
    co
    c.an
    co
    c.or
    co
    cF
    cfv
    #
    wss
    @3
    @7
    @8
    w3a
    @10
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
    cZ
    cF
    cfv
    cin
    cW
    cF
    cfv
    #
    c.pl
    co
    cV
    cF
    cfv
    #
    cin
    #
    @11
    @3
    @7
    @8
    @10
    @17
    wceq
    cB
    c.pl
    cF
    c.or
    cK
    c.le
    c.an
    c.pe
    cV
    cW
    cX
    cY
    cZ
    pl42lem.b
    pl42lem.l
    pl42lem.j
    pl42lem.m
    pl42lem.o
    pl42lem.f
    pl42lem.p
    pl42lem1N
    3impia
    @3
    @7
    @17
    @11
    wss
    @8
    @3
    @7
    wa
    #
    @17
    @14
    @15
    c.pl
    co
    @14
    @16
    c.pl
    co
    cin
    #
    @11
    cB
    c.pl
    cF
    c.or
    cK
    c.le
    c.an
    c.pe
    cV
    cW
    cX
    cY
    cZ
    pl42lem.b
    pl42lem.l
    pl42lem.j
    pl42lem.m
    pl42lem.o
    pl42lem.f
    pl42lem.p
    pl42lem3N
    @18
    @19
    @14
    @12
    @15
    c.pl
    co
    @13
    @16
    c.pl
    co
    cin
    c.pl
    co
    #
    @11
    @18
    @0
    @12
    cK
    cpsubsp
    cfv
    #
    wcel
    #
    @13
    @21
    wcel
    #
    @15
    @21
    wcel
    #
    @16
    @21
    wcel
    #
    @19
    @20
    wceq
    @0
    @1
    @2
    @7
    simpl1
    #
    @18
    cK
    clat
    wcel
    #
    @1
    @22
    @18
    @0
    @27
    @26
    cK
    hllat
    syl
    #
    @0
    @1
    @2
    @7
    simpl2
    cB
    @21
    cK
    cF
    cX
    pl42lem.b
    @21
    eqid
    #
    pl42lem.f
    pmapsub
    syl2anc
    @18
    @27
    @2
    @23
    @28
    @0
    @1
    @2
    @7
    simpl3
    cB
    @21
    cK
    cF
    cY
    pl42lem.b
    @29
    pl42lem.f
    pmapsub
    syl2anc
    @18
    @27
    @5
    @24
    @28
    @3
    @4
    @5
    @6
    simpr2
    cB
    @21
    cK
    cF
    cW
    pl42lem.b
    @29
    pl42lem.f
    pmapsub
    syl2anc
    @18
    @27
    @6
    @25
    @28
    @3
    @4
    @5
    @6
    simpr3
    cB
    @21
    cK
    cF
    cV
    pl42lem.b
    @29
    pl42lem.f
    pmapsub
    syl2anc
    c.pl
    @21
    cK
    @16
    @12
    @13
    @15
    @29
    pl42lem.p
    pmodl42N
    syl32anc
    cB
    c.pl
    cF
    c.or
    cK
    c.le
    c.an
    c.pe
    cV
    cW
    cX
    cY
    cZ
    pl42lem.b
    pl42lem.l
    pl42lem.j
    pl42lem.m
    pl42lem.o
    pl42lem.f
    pl42lem.p
    pl42lem2N
    eqsstrd
    sstrd
    3adant3
    eqsstrd
    3expia
end
