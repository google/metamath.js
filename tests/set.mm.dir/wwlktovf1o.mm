include "wcel.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wwlktovf1.mm"
include "a1i.mm"
include "wwlktovfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem wwlktovf1o
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vp: setvar p
  let vu: setvar u
  assume wrd2f1tovbij.d: |- D = { w e. Word V | ( ( # ` w ) = 2 /\ ( w ` 0 ) = P /\ { ( w ` 0 ) , ( w ` 1 ) } e. X ) }
  assume wrd2f1tovbij.r: |- R = { n e. V | { P , n } e. X }
  assume wrd2f1tovbij.f: |- F = ( t e. D |-> ( t ` 1 ) )

  disjoint D t
  disjoint P n
  disjoint P t
  disjoint P w
  disjoint n t
  disjoint n w
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V t
  disjoint V w
  disjoint X n
  disjoint X w
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  disjoint V x
  disjoint V y
  disjoint i x
  disjoint i y
  disjoint D p
  disjoint D u
  disjoint p u
  disjoint F u
  disjoint F p
  disjoint P p
  disjoint P u
  disjoint R p
  disjoint R u
  disjoint V p
  disjoint V u
  disjoint X u
  disjoint n p
  disjoint t u
  disjoint u w
  assert |- ( P e. V -> F : D -1-1-onto-> R )

  proof
    cP
    cV
    wcel
    #
    cD
    cR
    cF
    wf1
    #
    cD
    cR
    cF
    wfo
    cD
    cR
    cF
    wf1o
    @1
    @0
    vw
    vt
    cD
    cP
    cR
    vn
    cF
    cV
    cX
    wrd2f1tovbij.d
    wrd2f1tovbij.r
    wrd2f1tovbij.f
    wwlktovf1
    a1i
    vw
    vt
    cD
    cP
    cR
    vn
    cF
    cV
    cX
    wrd2f1tovbij.d
    wrd2f1tovbij.r
    wrd2f1tovbij.f
    wwlktovfo
    cD
    cR
    cF
    df-f1o
    sylanbrc
end
