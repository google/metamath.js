include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cdleme21c.mm"
include "3adant2r.mm"
include "simp2r.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem cdleme21at
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( S e. A /\ P =/= Q /\ -. S .<_ ( P .\/ Q ) ) /\ U .<_ ( S .\/ T ) ) /\ ( z e. A /\ ( P .\/ z ) = ( S .\/ z ) ) ) -> T =/= z )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    w3a
    #
    cS
    cA
    wcel
    cP
    cQ
    wne
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    vz
    cv
    #
    cA
    wcel
    cP
    @4
    c.or
    co
    cS
    @4
    c.or
    co
    #
    wceq
    wa
    #
    w3a
    #
    cU
    @5
    c.le
    wbr
    #
    wn
    #
    cT
    @4
    wne
    @0
    @1
    @6
    @9
    @3
    vz
    cA
    cP
    cQ
    cS
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21c
    3adant2r
    @7
    @8
    cT
    @4
    @7
    @3
    cT
    @4
    wceq
    #
    @8
    @0
    @1
    @3
    @6
    simp2r
    @10
    @2
    @5
    cU
    c.le
    cT
    @4
    cS
    c.or
    oveq2
    breq2d
    syl5ibcom
    necon3bd
    mpd
end
