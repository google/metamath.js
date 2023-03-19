include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "simpl3.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simpl1.mm"
include "clat.mm"
include "hllat.mm"
include "eqid.mm"
include "lplnbase.mm"
include "latmcl.mm"
include "syl3an.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "3ad2ant2.mm"
include "cvrexch.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "llncvrlpln.mm"
include "syl31anc.mm"
include "mpbird.mm"

theorem 2lplnmN
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  assume 2lplnm.j: |- .\/ = ( join ` K )
  assume 2lplnm.m: |- ./\ = ( meet ` K )
  assume 2lplnm.c: |- C = ( <o ` K )
  assume 2lplnm.n: |- N = ( LLines ` K )
  assume 2lplnm.p: |- P = ( LPlanes ` K )


  assert |- ( ( ( K e. HL /\ X e. P /\ Y e. P ) /\ X C ( X .\/ Y ) ) -> ( X ./\ Y ) e. N )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    w3a
    #
    cX
    cX
    cY
    c.or
    co
    cC
    wbr
    #
    wa
    #
    cX
    cY
    c.an
    co
    #
    cN
    wcel
    #
    @2
    @0
    @1
    @2
    @4
    simpl3
    @5
    @0
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    cY
    @8
    wcel
    #
    @6
    cY
    cC
    wbr
    #
    @7
    @2
    wb
    @0
    @1
    @2
    @4
    simpl1
    @3
    @9
    @4
    @0
    cK
    clat
    wcel
    @1
    cX
    @8
    wcel
    #
    @2
    @10
    @9
    cK
    hllat
    @8
    cP
    cK
    cX
    @8
    eqid
    #
    2lplnm.p
    lplnbase
    #
    @8
    cP
    cK
    cY
    @13
    2lplnm.p
    lplnbase
    #
    @8
    cK
    c.an
    cX
    cY
    @13
    2lplnm.m
    latmcl
    syl3an
    adantr
    @3
    @10
    @4
    @2
    @0
    @10
    @1
    @15
    3ad2ant3
    #
    adantr
    @3
    @11
    @4
    @3
    @0
    @12
    @10
    @11
    @4
    wb
    @0
    @1
    @2
    simp1
    @1
    @0
    @12
    @2
    @14
    3ad2ant2
    @16
    @8
    cC
    c.or
    cK
    c.an
    cX
    cY
    @13
    2lplnm.j
    2lplnm.m
    2lplnm.c
    cvrexch
    syl3anc
    biimpar
    @8
    cC
    cP
    cK
    cN
    @6
    cY
    @13
    2lplnm.c
    2lplnm.n
    2lplnm.p
    llncvrlpln
    syl31anc
    mpbird
end
