include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "catm.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "simpr2.mm"
include "inss1.mm"
include "paddss1.mm"
include "mpi.mm"
include "simpr3.mm"
include "sspadd2.mm"
include "ss2in.mm"

theorem pl42lem3N
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


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B /\ V e. B ) ) -> ( ( ( ( ( F ` X ) .+ ( F ` Y ) ) i^i ( F ` Z ) ) .+ ( F ` W ) ) i^i ( F ` V ) ) C_ ( ( ( ( F ` X ) .+ ( F ` Y ) ) .+ ( F ` W ) ) i^i ( ( ( F ` X ) .+ ( F ` Y ) ) .+ ( F ` V ) ) ) )

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
    @11
    @14
    c.pl
    co
    #
    wss
    #
    cV
    cF
    cfv
    #
    @11
    @18
    c.pl
    co
    #
    wss
    #
    @15
    @18
    cin
    @16
    @19
    cin
    wss
    @8
    @0
    @11
    cK
    catm
    cfv
    #
    wss
    #
    @14
    @21
    wss
    #
    @17
    @0
    @1
    @2
    @7
    simpl1
    #
    @8
    @0
    @9
    @21
    wss
    #
    @10
    @21
    wss
    #
    @22
    @24
    @8
    @0
    @1
    @25
    @24
    @0
    @1
    @2
    @7
    simpl2
    @21
    cB
    chlt
    cK
    cF
    cX
    pl42lem.b
    @21
    eqid
    #
    pl42lem.f
    pmapssat
    syl2anc
    @8
    @0
    @2
    @26
    @24
    @0
    @1
    @2
    @7
    simpl3
    @21
    cB
    chlt
    cK
    cF
    cY
    pl42lem.b
    @27
    pl42lem.f
    pmapssat
    syl2anc
    @21
    chlt
    c.pl
    cK
    @9
    @10
    @27
    pl42lem.p
    paddssat
    syl3anc
    #
    @8
    @0
    @5
    @23
    @24
    @3
    @4
    @5
    @6
    simpr2
    @21
    cB
    chlt
    cK
    cF
    cW
    pl42lem.b
    @27
    pl42lem.f
    pmapssat
    syl2anc
    @0
    @22
    @23
    w3a
    @13
    @11
    wss
    @17
    @11
    @12
    inss1
    @21
    chlt
    c.pl
    cK
    @13
    @11
    @14
    @27
    pl42lem.p
    paddss1
    mpi
    syl3anc
    @8
    @0
    @18
    @21
    wss
    #
    @22
    @20
    @24
    @8
    @0
    @6
    @29
    @24
    @3
    @4
    @5
    @6
    simpr3
    @21
    cB
    chlt
    cK
    cF
    cV
    pl42lem.b
    @27
    pl42lem.f
    pmapssat
    syl2anc
    @28
    @21
    chlt
    c.pl
    cK
    @18
    @11
    @27
    pl42lem.p
    sspadd2
    syl3anc
    @15
    @16
    @18
    @19
    ss2in
    syl2anc
end
