include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3l1.mm"
include "cdlemb2.mm"
include "syl221anc.mm"
include "nfv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfbr.mm"
include "simp111.mm"
include "simp112.mm"
include "simp113.mm"
include "simp121.mm"
include "simp122.mm"
include "simp123.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp3r.mm"
include "jca.mm"
include "simp2.mm"
include "simp3l.mm"
include "cdleme26e.mm"
include "syl333anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem cdleme26ee
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme26e.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme26e.f: |- F = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme26e.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( S .\/ z ) ./\ W ) ) )
  assume cdleme26e.o: |- O = ( ( P .\/ Q ) ./\ ( F .\/ ( ( T .\/ z ) ./\ W ) ) )
  assume cdleme26e.i: |- I = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme26e.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )

  disjoint u z
  disjoint A z
  disjoint A u
  disjoint B z
  disjoint B u
  disjoint H z
  disjoint .\/ z
  disjoint .\/ u
  disjoint K z
  disjoint .<_ z
  disjoint .<_ u
  disjoint ./\ z
  disjoint ./\ u
  disjoint N u
  disjoint O u
  disjoint P z
  disjoint P u
  disjoint Q z
  disjoint Q u
  disjoint S z
  disjoint S u
  disjoint T z
  disjoint T u
  disjoint U z
  disjoint U u
  disjoint W z
  disjoint W u
  disjoint V z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( V e. A /\ V .<_ W ) ) /\ ( ( P =/= Q /\ S .<_ ( P .\/ Q ) /\ T .<_ ( P .\/ Q ) ) /\ ( T .\/ V ) = ( P .\/ Q ) ) ) -> I .<_ ( E .\/ V ) )

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
    #
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
    #
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cT
    @11
    c.le
    wbr
    #
    w3a
    #
    cT
    cV
    c.or
    co
    @11
    wceq
    #
    wa
    #
    w3a
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @18
    @11
    c.le
    wbr
    wn
    #
    wa
    #
    vz
    cA
    wrex
    #
    cI
    cE
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    @0
    @1
    @3
    @4
    @10
    @22
    @0
    @1
    @3
    @4
    @9
    @16
    simp11l
    @0
    @1
    @3
    @4
    @9
    @16
    simp11r
    @2
    @3
    @4
    @9
    @16
    simp12
    @2
    @3
    @4
    @9
    @16
    simp13
    @10
    @12
    @13
    @15
    @5
    @9
    simp3l1
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vz
    cdleme26.l
    cdleme26.j
    cdleme26.a
    cdleme26.h
    cdlemb2
    syl221anc
    @17
    @21
    @24
    vz
    cA
    @17
    vz
    nfv
    vz
    cI
    @23
    c.le
    vz
    cI
    @21
    vu
    cv
    #
    cN
    wceq
    wi
    #
    vz
    cA
    wral
    #
    vu
    cB
    crio
    cdleme26e.i
    @27
    vz
    vu
    cB
    @26
    vz
    cA
    nfra1
    vz
    cB
    nfcv
    #
    nfriota
    nfcxfr
    vz
    c.le
    nfcv
    vz
    cE
    cV
    c.or
    vz
    cE
    @21
    @25
    cO
    wceq
    wi
    #
    vz
    cA
    wral
    #
    vu
    cB
    crio
    cdleme26e.e
    @30
    vz
    vu
    cB
    @29
    vz
    cA
    nfra1
    @28
    nfriota
    nfcxfr
    vz
    c.or
    nfcv
    vz
    cV
    nfcv
    nfov
    nfbr
    @17
    @18
    cA
    wcel
    #
    @21
    @24
    @17
    @31
    @21
    w3a
    #
    @2
    @3
    @4
    @6
    @7
    @8
    @14
    @15
    @20
    wa
    @31
    @19
    wa
    @24
    @2
    @3
    @4
    @9
    @16
    @31
    @21
    simp111
    @2
    @3
    @4
    @9
    @16
    @31
    @21
    simp112
    @2
    @3
    @4
    @9
    @16
    @31
    @21
    simp113
    @6
    @7
    @8
    @5
    @16
    @31
    @21
    simp121
    @6
    @7
    @8
    @5
    @16
    @31
    @21
    simp122
    @6
    @7
    @8
    @5
    @16
    @31
    @21
    simp123
    @14
    @15
    @5
    @9
    @31
    @21
    simp13l
    @32
    @15
    @20
    @14
    @15
    @5
    @9
    @31
    @21
    simp13r
    @17
    @31
    @19
    @20
    simp3r
    jca
    @32
    @31
    @19
    @17
    @31
    @21
    simp2
    @17
    @31
    @19
    @20
    simp3l
    jca
    vz
    vu
    cA
    cB
    cP
    cQ
    cS
    cT
    cU
    cE
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26e.u
    cdleme26e.f
    cdleme26e.n
    cdleme26e.o
    cdleme26e.i
    cdleme26e.e
    cdleme26e
    syl333anc
    3exp
    rexlimd
    mpd
end
