include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "ccnv.mm"
include "simp3.mm"
include "wceq.mm"
include "wrel.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "3adant3.mm"
include "f1orel.mm"
include "syl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "cnveq.mm"
include "sylan9req.mm"
include "cnvresid.mm"
include "syl6eq.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem ltrncnvnid
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume ltrn1o.b: |- B = ( Base ` K )
  assume ltrn1o.h: |- H = ( LHyp ` K )
  assume ltrn1o.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ F =/= ( _I |` B ) ) -> `' F =/= ( _I |` B ) )

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
    cF
    cid
    cB
    cres
    #
    wne
    #
    w3a
    #
    @3
    cF
    ccnv
    #
    @2
    wne
    @0
    @1
    @3
    simp3
    @4
    @5
    @2
    cF
    @2
    @4
    @5
    @2
    wceq
    #
    cF
    @2
    wceq
    @4
    @6
    wa
    cF
    @2
    ccnv
    #
    @2
    @4
    @6
    cF
    @5
    ccnv
    #
    @7
    @4
    cF
    wrel
    #
    @8
    cF
    wceq
    @4
    cB
    cB
    cF
    wf1o
    #
    @9
    @0
    @1
    @10
    @3
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    ltrn1o.b
    ltrn1o.h
    ltrn1o.t
    ltrn1o
    3adant3
    cB
    cB
    cF
    f1orel
    syl
    cF
    dfrel2
    sylib
    @5
    @2
    cnveq
    sylan9req
    cB
    cnvresid
    syl6eq
    ex
    necon3d
    mpd
end
