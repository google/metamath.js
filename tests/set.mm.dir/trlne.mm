include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "simp3r.mm"
include "wceq.mm"
include "trlle.mm"
include "3adant3.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem trlne
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trlne.l: |- .<_ = ( le ` K )
  assume trlne.a: |- A = ( Atoms ` K )
  assume trlne.h: |- H = ( LHyp ` K )
  assume trlne.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlne.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> P =/= ( R ` F ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    @4
    cP
    cF
    cR
    cfv
    #
    wne
    @0
    @1
    @2
    @4
    simp3r
    @6
    @3
    cP
    @7
    @6
    @3
    cP
    @7
    wceq
    @7
    cW
    c.le
    wbr
    #
    @0
    @1
    @8
    @5
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    trlne.l
    trlne.h
    trlne.t
    trlne.r
    trlle
    3adant3
    cP
    @7
    cW
    c.le
    breq1
    syl5ibrcom
    necon3bd
    mpd
end
