include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp21l.mm"
include "simp23.mm"
include "simp22.mm"
include "cdlemk1.mm"
include "syl222anc.mm"
include "simp13.mm"
include "cdlemk2.mm"
include "syl221anc.mm"
include "oveq12d.mm"
include "simp21r.mm"
include "simp33.mm"
include "simp31.mm"
include "simp32.mm"
include "jca.mm"
include "cdlemk5a.mm"
include "syl233anc.mm"
include "eqbrtrd.mm"

theorem cdlemk5
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( N e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` F ) ) ) -> ( ( P .\/ ( N ` P ) ) ./\ ( ( G ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) .<_ ( ( X ` P ) .\/ ( R ` ( X o. `' F ) ) ) )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cN
    cT
    wcel
    #
    cX
    cT
    wcel
    #
    wa
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    @13
    wne
    #
    cG
    cR
    cfv
    @10
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cN
    cfv
    c.or
    co
    #
    cP
    cG
    cfv
    cG
    cF
    ccnv
    #
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    cP
    cF
    cfv
    #
    @10
    c.or
    co
    #
    @23
    @21
    c.or
    co
    #
    c.an
    co
    #
    cP
    cX
    cfv
    cX
    @20
    ccom
    cR
    cfv
    c.or
    co
    #
    c.le
    @18
    @19
    @24
    @22
    @25
    c.an
    @18
    @0
    @1
    @3
    @6
    @11
    @9
    @19
    @24
    wceq
    @0
    @1
    @3
    @4
    @12
    @17
    simp11l
    #
    @0
    @1
    @3
    @4
    @12
    @17
    simp11r
    #
    @2
    @3
    @4
    @12
    @17
    simp12
    #
    @6
    @7
    @9
    @11
    @5
    @17
    simp21l
    @5
    @8
    @9
    @11
    @17
    simp23
    @5
    @8
    @9
    @11
    @17
    simp22
    #
    cA
    cB
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    cN
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk1
    syl222anc
    @18
    @0
    @1
    @3
    @4
    @9
    @22
    @25
    wceq
    @28
    @29
    @30
    @2
    @3
    @4
    @12
    @17
    simp13
    #
    @31
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk2
    syl221anc
    oveq12d
    @18
    @0
    @1
    @3
    @4
    @7
    @16
    @14
    @15
    wa
    @9
    @26
    @27
    c.le
    wbr
    @28
    @29
    @30
    @32
    @6
    @7
    @9
    @11
    @5
    @17
    simp21r
    @5
    @12
    @14
    @15
    @16
    simp33
    @18
    @14
    @15
    @5
    @12
    @14
    @15
    @16
    simp31
    @5
    @12
    @14
    @15
    @16
    simp32
    jca
    @31
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk5a
    syl233anc
    eqbrtrd
end
