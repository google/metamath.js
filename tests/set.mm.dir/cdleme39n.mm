include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "eqid.mm"
include "cdleme38n.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp22l.mm"
include "simp22r.mm"
include "simp311.mm"
include "simp32l.mm"
include "cdleme39a.mm"
include "syl322anc.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp312.mm"
include "simp33l.mm"
include "3netr4d.mm"

theorem cdleme39n
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume cdleme39.l: |- .<_ = ( le ` K )
  assume cdleme39.j: |- .\/ = ( join ` K )
  assume cdleme39.m: |- ./\ = ( meet ` K )
  assume cdleme39.a: |- A = ( Atoms ` K )
  assume cdleme39.h: |- H = ( LHyp ` K )
  assume cdleme39.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme39.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme39.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme39.y: |- Y = ( ( u .\/ U ) ./\ ( Q .\/ ( ( P .\/ u ) ./\ W ) ) )
  assume cdleme39.z: |- Z = ( ( P .\/ Q ) ./\ ( Y .\/ ( ( S .\/ u ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ R =/= S ) /\ ( ( t e. A /\ -. t .<_ W ) /\ -. t .<_ ( P .\/ Q ) ) /\ ( ( u e. A /\ -. u .<_ W ) /\ -. u .<_ ( P .\/ Q ) ) ) ) -> G =/= Z )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
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
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
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
    #
    c.le
    wbr
    #
    cS
    @16
    c.le
    wbr
    #
    cR
    cS
    wne
    #
    w3a
    #
    vt
    cv
    #
    cA
    wcel
    @21
    cW
    c.le
    wbr
    wn
    wa
    #
    @21
    @16
    c.le
    wbr
    wn
    #
    wa
    #
    vu
    cv
    #
    cA
    wcel
    @25
    cW
    c.le
    wbr
    wn
    wa
    #
    @25
    @16
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    w3a
    #
    cR
    @21
    cE
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    cE
    @21
    cR
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cS
    @25
    cY
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    cY
    @25
    cS
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cG
    cZ
    vu
    vt
    cA
    cY
    cP
    cQ
    cR
    cS
    cU
    cE
    @32
    @34
    cH
    c.or
    cK
    c.le
    c.an
    @31
    cW
    @33
    cdleme39.l
    cdleme39.j
    cdleme39.m
    cdleme39.a
    cdleme39.h
    cdleme39.u
    cdleme39.e
    cdleme39.y
    @31
    eqid
    #
    @33
    eqid
    #
    @32
    eqid
    @34
    eqid
    cdleme38n
    @30
    @0
    @1
    @4
    @9
    @10
    @17
    @22
    cG
    @32
    wceq
    @0
    @3
    @6
    @15
    @29
    simp11
    #
    @1
    @2
    @0
    @6
    @15
    @29
    simp12l
    #
    @4
    @5
    @0
    @3
    @15
    @29
    simp13l
    #
    @9
    @10
    @8
    @14
    @7
    @29
    simp22l
    @9
    @10
    @8
    @14
    @7
    @29
    simp22r
    @17
    @18
    @19
    @24
    @28
    @7
    @15
    simp311
    @22
    @23
    @20
    @28
    @7
    @15
    simp32l
    vt
    cA
    cP
    cQ
    cR
    cU
    cE
    cG
    cH
    c.or
    cK
    c.le
    c.an
    @31
    cW
    cdleme39.l
    cdleme39.j
    cdleme39.m
    cdleme39.a
    cdleme39.h
    cdleme39.u
    cdleme39.e
    cdleme39.g
    @35
    cdleme39a
    syl322anc
    @30
    @0
    @1
    @4
    @12
    @13
    @18
    @26
    cZ
    @34
    wceq
    @37
    @38
    @39
    @12
    @13
    @8
    @11
    @7
    @29
    simp23l
    @12
    @13
    @8
    @11
    @7
    @29
    simp23r
    @17
    @18
    @19
    @24
    @28
    @7
    @15
    simp312
    @26
    @27
    @20
    @24
    @7
    @15
    simp33l
    vu
    cA
    cP
    cQ
    cS
    cU
    cY
    cZ
    cH
    c.or
    cK
    c.le
    c.an
    @33
    cW
    cdleme39.l
    cdleme39.j
    cdleme39.m
    cdleme39.a
    cdleme39.h
    cdleme39.u
    cdleme39.y
    cdleme39.z
    @36
    cdleme39a
    syl322anc
    3netr4d
end
