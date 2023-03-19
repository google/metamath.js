include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp33.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpr.mm"
include "cdleme35h.mm"
include "syl113anc.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdleme35h2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme35.l: |- .<_ = ( le ` K )
  assume cdleme35.j: |- .\/ = ( join ` K )
  assume cdleme35.m: |- ./\ = ( meet ` K )
  assume cdleme35.a: |- A = ( Atoms ` K )
  assume cdleme35.h: |- H = ( LHyp ` K )
  assume cdleme35.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme35.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme35.g: |- G = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ R =/= S ) ) -> F =/= G )

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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cQ
    wne
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    @2
    c.le
    wbr
    wn
    #
    cR
    cS
    wne
    #
    w3a
    #
    w3a
    #
    @5
    cF
    cG
    wne
    @0
    @1
    @3
    @4
    @5
    simp33
    @7
    cF
    cG
    cR
    cS
    @7
    cF
    cG
    wceq
    #
    cR
    cS
    wceq
    #
    @7
    @8
    wa
    @0
    @1
    @3
    @4
    @8
    @9
    @0
    @1
    @6
    @8
    simpl1
    @0
    @1
    @6
    @8
    simpl2
    @3
    @4
    @5
    @0
    @1
    @8
    simpl31
    @3
    @4
    @5
    @0
    @1
    @8
    simpl32
    @7
    @8
    simpr
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    cdleme35.g
    cdleme35h
    syl113anc
    ex
    necon3d
    mpd
end
