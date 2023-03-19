include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cp0.mm"
include "cfv.mm"
include "clat.mm"
include "cbs.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp23.mm"
include "atbase.mm"
include "syl.mm"
include "latmcom.mm"
include "simp3r.mm"
include "clc.mm"
include "wi.mm"
include "hlcvl.mm"
include "simp3l.mm"
include "necomd.mm"
include "cvlatexch1.mm"
include "syl131anc.mm"
include "mtod.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "atnle.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem cdleme20zN
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume cdleme20z.l: |- .<_ = ( le ` K )
  assume cdleme20z.j: |- .\/ = ( join ` K )
  assume cdleme20z.m: |- ./\ = ( meet ` K )
  assume cdleme20z.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( S =/= T /\ -. R .<_ ( S .\/ T ) ) ) -> ( ( S .\/ R ) ./\ T ) = ( 0. ` K ) )

  proof
    cK
    chlt
    wcel
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    w3a
    #
    cS
    cT
    wne
    #
    cR
    cS
    cT
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cS
    cR
    c.or
    co
    #
    cT
    c.an
    co
    #
    cT
    @10
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    @9
    cK
    clat
    wcel
    #
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    cT
    @15
    wcel
    #
    @11
    @12
    wceq
    @0
    @4
    @14
    @8
    cK
    hllat
    3ad2ant1
    @9
    @0
    @2
    @1
    @16
    @0
    @4
    @8
    simp1
    @0
    @1
    @2
    @3
    @8
    simp22
    #
    @0
    @1
    @2
    @3
    @8
    simp21
    #
    cA
    @15
    c.or
    cK
    cS
    cR
    @15
    eqid
    #
    cdleme20z.j
    cdleme20z.a
    hlatjcl
    syl3anc
    #
    @9
    @3
    @17
    @0
    @1
    @2
    @3
    @8
    simp23
    #
    cA
    @15
    cT
    cK
    @20
    cdleme20z.a
    atbase
    syl
    @15
    cK
    c.an
    @10
    cT
    @20
    cdleme20z.m
    latmcom
    syl3anc
    @9
    cT
    @10
    c.le
    wbr
    #
    wn
    #
    @12
    @13
    wceq
    #
    @9
    @23
    @6
    @0
    @4
    @5
    @7
    simp3r
    @9
    cK
    clc
    wcel
    #
    @3
    @1
    @2
    cT
    cS
    wne
    @23
    @6
    wi
    @0
    @4
    @26
    @8
    cK
    hlcvl
    3ad2ant1
    @22
    @19
    @18
    @9
    cS
    cT
    @0
    @4
    @5
    @7
    simp3l
    necomd
    cA
    cT
    cR
    cS
    c.or
    cK
    c.le
    cdleme20z.l
    cdleme20z.j
    cdleme20z.a
    cvlatexch1
    syl131anc
    mtod
    @9
    cK
    cal
    wcel
    #
    @3
    @16
    @24
    @25
    wb
    @0
    @4
    @27
    @8
    cK
    hlatl
    3ad2ant1
    @22
    @21
    cA
    @15
    cT
    cK
    c.le
    c.an
    @10
    @13
    @20
    cdleme20z.l
    cdleme20z.m
    @13
    eqid
    cdleme20z.a
    atnle
    syl3anc
    mpbid
    eqtrd
end
