include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "cvv.mm"
include "cn0.mm"
include "cword.mm"
include "w3a.mm"
include "wwlknbp.mm"
include "wwlksnextinj.mm"
include "3ad2ant2.mm"
include "syl.mm"
include "wwlksnextsur.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem wwlksnextbij0
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cR: class R
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vd: setvar d
  let vx: setvar x
  let vr: setvar r
  assume wwlksnextbij0.v: |- V = ( Vtx ` G )
  assume wwlksnextbij0.e: |- E = ( Edg ` G )
  assume wwlksnextbij0.d: |- D = { w e. Word V | ( ( # ` w ) = ( N + 2 ) /\ ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) }
  assume wwlksnextbij.r: |- R = { n e. V | { ( lastS ` W ) , n } e. E }
  assume wwlksnextbij.f: |- F = ( t e. D |-> ( lastS ` t ) )

  disjoint G w
  disjoint N w
  disjoint W w
  disjoint D t
  disjoint E n
  disjoint E w
  disjoint N t
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V w
  disjoint W n
  disjoint n t
  disjoint N n
  disjoint n w
  disjoint G i
  disjoint i w
  disjoint N i
  disjoint D d
  disjoint D x
  disjoint d x
  disjoint F d
  disjoint F x
  disjoint N d
  disjoint N x
  disjoint d t
  disjoint d w
  disjoint t x
  disjoint w x
  disjoint D r
  disjoint d r
  disjoint E d
  disjoint F r
  disjoint G d
  disjoint G r
  disjoint N r
  disjoint d n
  disjoint n r
  disjoint r t
  disjoint r w
  disjoint R d
  disjoint R r
  disjoint V d
  disjoint W d
  disjoint W i
  disjoint W r
  disjoint d i
  disjoint i r
  assert |- ( W e. ( N WWalksN G ) -> F : D -1-1-onto-> R )

  proof
    cW
    cN
    cG
    cwwlksn
    co
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
    @0
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    w3a
    @1
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlknbp
    @3
    @2
    @1
    @4
    vw
    vt
    cD
    cR
    vn
    cE
    cF
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnextbij0.d
    wwlksnextbij.r
    wwlksnextbij.f
    wwlksnextinj
    3ad2ant2
    syl
    vw
    vt
    cD
    cR
    vn
    cE
    cF
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnextbij0.d
    wwlksnextbij.r
    wwlksnextbij.f
    wwlksnextsur
    cD
    cR
    cF
    df-f1o
    sylanbrc
end
