include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "simpll1.mm"
include "simpl21.mm"
include "adantr.mm"
include "simpl22.mm"
include "simp23.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "simpll3.mm"
include "cdlemd4.mm"
include "syl131anc.mm"
include "simpl3l.mm"
include "pm2.61ne.mm"
include "simpl1.mm"
include "simpl23.mm"
include "jca.mm"
include "simpl3.mm"
include "cdlemd2.mm"
include "pm2.61dan.mm"

theorem cdlemd5
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vs: setvar s
  assume cdlemd4.l: |- .<_ = ( le ` K )
  assume cdlemd4.j: |- .\/ = ( join ` K )
  assume cdlemd4.a: |- A = ( Atoms ` K )
  assume cdlemd4.h: |- H = ( LHyp ` K )
  assume cdlemd4.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ R e. A ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ P =/= Q ) /\ ( ( F ` P ) = ( G ` P ) /\ ( F ` Q ) = ( G ` Q ) ) ) -> ( F ` R ) = ( G ` R ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cG
    cT
    wcel
    wa
    cR
    cA
    wcel
    w3a
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cF
    cfv
    #
    cP
    cG
    cfv
    #
    wceq
    #
    cQ
    cF
    cfv
    cQ
    cG
    cfv
    wceq
    #
    wa
    #
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    cR
    cF
    cfv
    #
    cR
    cG
    cfv
    #
    wceq
    #
    @10
    @11
    wa
    #
    @14
    @7
    cR
    cP
    cR
    cP
    wceq
    @12
    @5
    @13
    @6
    cR
    cP
    cF
    fveq2
    cR
    cP
    cG
    fveq2
    eqeq12d
    @15
    cR
    cP
    wne
    #
    wa
    #
    @0
    @1
    @2
    @3
    @11
    @16
    w3a
    @9
    @14
    @0
    @4
    @9
    @11
    @16
    simpll1
    @15
    @1
    @16
    @1
    @2
    @3
    @0
    @9
    @11
    simpl21
    adantr
    @15
    @2
    @16
    @1
    @2
    @3
    @0
    @9
    @11
    simpl22
    adantr
    @17
    @3
    @11
    @16
    @10
    @3
    @11
    @16
    @0
    @1
    @2
    @3
    @9
    simp23
    ad2antrr
    @10
    @11
    @16
    simplr
    @15
    @16
    simpr
    3jca
    @0
    @4
    @9
    @11
    @16
    simpll3
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    cdlemd4
    syl131anc
    @7
    @8
    @0
    @4
    @11
    simpl3l
    pm2.61ne
    @10
    @11
    wn
    #
    wa
    #
    @0
    @1
    @2
    @3
    @18
    wa
    @9
    @14
    @0
    @4
    @9
    @18
    simpl1
    @1
    @2
    @3
    @0
    @9
    @18
    simpl21
    @1
    @2
    @3
    @0
    @9
    @18
    simpl22
    @19
    @3
    @18
    @1
    @2
    @3
    @0
    @9
    @18
    simpl23
    @10
    @18
    simpr
    jca
    @0
    @4
    @9
    @18
    simpl3
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    cdlemd2
    syl131anc
    pm2.61dan
end
