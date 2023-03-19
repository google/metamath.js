include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cal.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "hlatl.mm"
include "3ad2ant1.mm"
include "clat.mm"
include "hllat.mm"
include "simp22.mm"
include "eqid.mm"
include "llnbase.mm"
include "syl.mm"
include "simp23.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp21.mm"
include "simp3.mm"
include "wb.mm"
include "atbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "atlen0.mm"
include "syl31anc.mm"

theorem 2llnm4
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume 2llnm4.l: |- .<_ = ( le ` K )
  assume 2llnm4.m: |- ./\ = ( meet ` K )
  assume 2llnm4.z: |- .0. = ( 0. ` K )
  assume 2llnm4.a: |- A = ( Atoms ` K )
  assume 2llnm4.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. N /\ Y e. N ) /\ ( P .<_ X /\ P .<_ Y ) ) -> ( X ./\ Y ) =/= .0. )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    cP
    cY
    c.le
    wbr
    wa
    #
    w3a
    #
    cK
    cal
    wcel
    #
    cX
    cY
    c.an
    co
    #
    cK
    cbs
    cfv
    #
    wcel
    #
    @1
    cP
    @8
    c.le
    wbr
    #
    @8
    c.0
    wne
    @0
    @4
    @7
    @5
    cK
    hlatl
    3ad2ant1
    @6
    cK
    clat
    wcel
    #
    cX
    @9
    wcel
    #
    cY
    @9
    wcel
    #
    @10
    @0
    @4
    @12
    @5
    cK
    hllat
    3ad2ant1
    #
    @6
    @2
    @13
    @0
    @1
    @2
    @3
    @5
    simp22
    @9
    cK
    cN
    cX
    @9
    eqid
    #
    2llnm4.n
    llnbase
    syl
    #
    @6
    @3
    @14
    @0
    @1
    @2
    @3
    @5
    simp23
    @9
    cK
    cN
    cY
    @16
    2llnm4.n
    llnbase
    syl
    #
    @9
    cK
    c.an
    cX
    cY
    @16
    2llnm4.m
    latmcl
    syl3anc
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    @6
    @5
    @11
    @0
    @4
    @5
    simp3
    @6
    @12
    cP
    @9
    wcel
    #
    @13
    @14
    @5
    @11
    wb
    @15
    @6
    @1
    @20
    @19
    cA
    @9
    cP
    cK
    @16
    2llnm4.a
    atbase
    syl
    @17
    @18
    @9
    cK
    c.le
    c.an
    cP
    cX
    cY
    @16
    2llnm4.l
    2llnm4.m
    latlem12
    syl13anc
    mpbid
    cA
    @9
    cP
    cK
    c.le
    @8
    c.0
    @16
    2llnm4.l
    2llnm4.z
    2llnm4.a
    atlen0
    syl31anc
end
