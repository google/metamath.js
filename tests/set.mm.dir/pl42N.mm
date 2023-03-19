include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "cpmap.mm"
include "wss.mm"
include "cpadd.mm"
include "eqid.mm"
include "pl42lem4N.mm"
include "wb.mm"
include "simpl1.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "latmcl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "pmaple.mm"
include "sylibrd.mm"

theorem pl42N
  let cB: class B
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
  assume pl42.b: |- B = ( Base ` K )
  assume pl42.l: |- .<_ = ( le ` K )
  assume pl42.j: |- .\/ = ( join ` K )
  assume pl42.m: |- ./\ = ( meet ` K )
  assume pl42.o: |- ._|_ = ( oc ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B /\ V e. B ) ) -> ( ( X .<_ ( ._|_ ` Y ) /\ Z .<_ ( ._|_ ` W ) ) -> ( ( ( ( X .\/ Y ) ./\ Z ) .\/ W ) ./\ V ) .<_ ( ( X .\/ Y ) .\/ ( ( X .\/ W ) ./\ ( Y .\/ V ) ) ) ) )

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
    #
    cK
    cpmap
    cfv
    #
    cfv
    @9
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
    c.or
    co
    #
    @13
    cfv
    wss
    #
    @12
    @17
    c.le
    wbr
    #
    cB
    cK
    cpadd
    cfv
    #
    @13
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
    pl42.b
    pl42.l
    pl42.j
    pl42.m
    pl42.o
    @13
    eqid
    #
    @20
    eqid
    pl42lem4N
    @8
    @0
    @12
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    @19
    @18
    wb
    @0
    @1
    @2
    @7
    simpl1
    #
    @8
    cK
    clat
    wcel
    #
    @11
    cB
    wcel
    #
    @6
    @22
    @8
    @0
    @25
    @24
    cK
    hllat
    syl
    #
    @8
    @25
    @10
    cB
    wcel
    #
    @5
    @26
    @27
    @8
    @25
    @9
    cB
    wcel
    #
    @4
    @28
    @27
    @8
    @25
    @1
    @2
    @29
    @27
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
    pl42.b
    pl42.j
    latjcl
    syl3anc
    #
    @3
    @4
    @5
    @6
    simpr1
    cB
    cK
    c.an
    @9
    cZ
    pl42.b
    pl42.m
    latmcl
    syl3anc
    @3
    @4
    @5
    @6
    simpr2
    #
    cB
    c.or
    cK
    @10
    cW
    pl42.b
    pl42.j
    latjcl
    syl3anc
    @3
    @4
    @5
    @6
    simpr3
    #
    cB
    cK
    c.an
    @11
    cV
    pl42.b
    pl42.m
    latmcl
    syl3anc
    @8
    @25
    @29
    @16
    cB
    wcel
    #
    @23
    @27
    @32
    @8
    @25
    @14
    cB
    wcel
    #
    @15
    cB
    wcel
    #
    @35
    @27
    @8
    @25
    @1
    @5
    @36
    @27
    @30
    @33
    cB
    c.or
    cK
    cX
    cW
    pl42.b
    pl42.j
    latjcl
    syl3anc
    @8
    @25
    @2
    @6
    @37
    @27
    @31
    @34
    cB
    c.or
    cK
    cY
    cV
    pl42.b
    pl42.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @14
    @15
    pl42.b
    pl42.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    @9
    @16
    pl42.b
    pl42.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    @13
    @12
    @17
    pl42.b
    pl42.l
    @21
    pmaple
    syl3anc
    sylibrd
end
