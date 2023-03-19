include "cn.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "clwwlkf1.mm"
include "clwwlkfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem clwwlkf1o
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vi: setvar i
  let cP: class P
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vp: setvar p
  assume clwwlkbij.d: |- D = { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) }
  assume clwwlkbij.f: |- F = ( t e. D |-> ( t substr <. 0 , N >. ) )

  disjoint G w
  disjoint N w
  disjoint D t
  disjoint G t
  disjoint t w
  disjoint N t
  disjoint G i
  disjoint N i
  disjoint P i
  disjoint P w
  disjoint i t
  disjoint W t
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint i x
  disjoint i y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  disjoint D p
  disjoint F p
  disjoint G p
  disjoint G x
  disjoint i p
  disjoint i w
  disjoint p w
  disjoint p x
  disjoint N p
  assert |- ( N e. NN -> F : D -1-1-onto-> ( N ClWWalksN G ) )

  proof
    cN
    cn
    wcel
    cD
    cN
    cG
    cclwwlkn
    co
    #
    cF
    wf1
    cD
    @0
    cF
    wfo
    cD
    @0
    cF
    wf1o
    vw
    vt
    cD
    cF
    cG
    cN
    clwwlkbij.d
    clwwlkbij.f
    clwwlkf1
    vw
    vt
    cD
    cF
    cG
    cN
    clwwlkbij.d
    clwwlkbij.f
    clwwlkfo
    cD
    @0
    cF
    df-f1o
    sylanbrc
end
