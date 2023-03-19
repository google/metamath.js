include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "simpr.mm"
include "fveq1d.mm"
include "simpl3l.mm"
include "atbase.mm"
include "fvresi.mm"
include "3syl.mm"
include "eqtrd.mm"
include "ex.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "ltrnnidn.mm"
include "syl121anc.mm"
include "necon4d.mm"
include "impbid.mm"

theorem ltrnideq
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnnidn.b: |- B = ( Base ` K )
  assume ltrnnidn.l: |- .<_ = ( le ` K )
  assume ltrnnidn.a: |- A = ( Atoms ` K )
  assume ltrnnidn.h: |- H = ( LHyp ` K )
  assume ltrnnidn.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( F = ( _I |` B ) <-> ( F ` P ) = P ) )

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
    wn
    #
    wa
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wceq
    #
    cP
    cF
    cfv
    #
    cP
    wceq
    #
    @5
    @7
    @9
    @5
    @7
    wa
    #
    @8
    cP
    @6
    cfv
    #
    cP
    @10
    cP
    cF
    @6
    @5
    @7
    simpr
    fveq1d
    @10
    @2
    cP
    cB
    wcel
    @11
    cP
    wceq
    @2
    @3
    @0
    @1
    @7
    simpl3l
    cA
    cB
    cP
    cK
    ltrnnidn.b
    ltrnnidn.a
    atbase
    cB
    cP
    fvresi
    3syl
    eqtrd
    ex
    @5
    cF
    @6
    @8
    cP
    @5
    cF
    @6
    wne
    #
    @8
    cP
    wne
    #
    @5
    @12
    wa
    @0
    @1
    @12
    @4
    @13
    @0
    @1
    @4
    @12
    simpl1
    @0
    @1
    @4
    @12
    simpl2
    @5
    @12
    simpr
    @0
    @1
    @4
    @12
    simpl3
    cA
    cB
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrnnidn.b
    ltrnnidn.l
    ltrnnidn.a
    ltrnnidn.h
    ltrnnidn.t
    ltrnnidn
    syl121anc
    ex
    necon4d
    impbid
end
