include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "cdlemednpq.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22.mm"
include "cdlemeulpq.mm"
include "syl22anc.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem cdlemednuN
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemeda.l: |- .<_ = ( le ` K )
  assume cdlemeda.j: |- .\/ = ( join ` K )
  assume cdlemeda.m: |- ./\ = ( meet ` K )
  assume cdlemeda.a: |- A = ( Atoms ` K )
  assume cdlemeda.h: |- H = ( LHyp ` K )
  assume cdlemeda.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdlemednu.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> D =/= U )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    cS
    @7
    c.le
    wbr
    wn
    w3a
    #
    w3a
    #
    cD
    @7
    c.le
    wbr
    #
    wn
    cD
    cU
    wne
    cA
    cD
    cP
    cQ
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemeda.l
    cdlemeda.j
    cdlemeda.m
    cdlemeda.a
    cdlemeda.h
    cdlemeda.d
    cdlemednpq
    @9
    @10
    cD
    cU
    @9
    @10
    cD
    cU
    wceq
    cU
    @7
    c.le
    wbr
    #
    @9
    @0
    @1
    @3
    @4
    @11
    @0
    @1
    @6
    @8
    simp1l
    @0
    @1
    @6
    @8
    simp1r
    @2
    @3
    @4
    @5
    @8
    simp21
    @2
    @3
    @4
    @5
    @8
    simp22
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemeda.l
    cdlemeda.j
    cdlemeda.m
    cdlemeda.a
    cdlemeda.h
    cdlemednu.u
    cdlemeulpq
    syl22anc
    cD
    cU
    @7
    c.le
    breq1
    syl5ibrcom
    necon3bd
    mpd
end
