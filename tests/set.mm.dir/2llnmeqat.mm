include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "simp3r.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "3ad2ant1.mm"
include "simp23.mm"
include "cp0.mm"
include "cfv.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3l.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "llnbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbird.mm"
include "2llnm4.mm"
include "syl131anc.mm"
include "2llnmat.mm"
include "syl32anc.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem 2llnmeqat
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  assume 2llnmeqat.l: |- .<_ = ( le ` K )
  assume 2llnmeqat.m: |- ./\ = ( meet ` K )
  assume 2llnmeqat.a: |- A = ( Atoms ` K )
  assume 2llnmeqat.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ ( X e. N /\ Y e. N /\ P e. A ) /\ ( X =/= Y /\ P .<_ ( X ./\ Y ) ) ) -> P = ( X ./\ Y ) )

  proof
    cK
    chlt
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
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cY
    wne
    #
    cP
    cX
    cY
    c.an
    co
    #
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @7
    cP
    @6
    wceq
    #
    @0
    @4
    @5
    @7
    simp3r
    #
    @9
    cK
    cal
    wcel
    #
    @3
    @6
    cA
    wcel
    #
    @7
    @10
    wb
    @0
    @4
    @12
    @8
    cK
    hlatl
    3ad2ant1
    @0
    @1
    @2
    @3
    @8
    simp23
    #
    @9
    @0
    @1
    @2
    @5
    @6
    cK
    cp0
    cfv
    #
    wne
    #
    @13
    @0
    @4
    @8
    simp1
    #
    @0
    @1
    @2
    @3
    @8
    simp21
    #
    @0
    @1
    @2
    @3
    @8
    simp22
    #
    @0
    @4
    @5
    @7
    simp3l
    @9
    @0
    @3
    @1
    @2
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
    @16
    @17
    @14
    @18
    @19
    @9
    @20
    @7
    @11
    @9
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cX
    @22
    wcel
    #
    cY
    @22
    wcel
    #
    @20
    @7
    wb
    @0
    @4
    @21
    @8
    cK
    hllat
    3ad2ant1
    @9
    @3
    @23
    @14
    cA
    @22
    cP
    cK
    @22
    eqid
    #
    2llnmeqat.a
    atbase
    syl
    @9
    @1
    @24
    @18
    @22
    cK
    cN
    cX
    @26
    2llnmeqat.n
    llnbase
    syl
    @9
    @2
    @25
    @19
    @22
    cK
    cN
    cY
    @26
    2llnmeqat.n
    llnbase
    syl
    @22
    cK
    c.le
    c.an
    cP
    cX
    cY
    @26
    2llnmeqat.l
    2llnmeqat.m
    latlem12
    syl13anc
    mpbird
    cA
    cP
    cK
    c.le
    c.an
    cN
    cX
    cY
    @15
    2llnmeqat.l
    2llnmeqat.m
    @15
    eqid
    #
    2llnmeqat.a
    2llnmeqat.n
    2llnm4
    syl131anc
    cA
    cK
    c.an
    cN
    cX
    cY
    @15
    2llnmeqat.m
    @27
    2llnmeqat.a
    2llnmeqat.n
    2llnmat
    syl32anc
    cA
    cP
    @6
    cK
    c.le
    2llnmeqat.l
    2llnmeqat.a
    atcmp
    syl3anc
    mpbid
end
