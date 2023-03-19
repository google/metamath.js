include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "c1o.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wb.mm"
include "pw2f1o2val.mm"
include "eleq2d.mm"
include "adantr.mm"
include "wf.mm"
include "wfn.mm"
include "elmapi.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3syl.mm"
include "baibd.mm"
include "bitrd.mm"

theorem pw2f1o2val2
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cV: class V
  assume pw2f1o2.f: |- F = ( x e. ( 2o ^m A ) |-> ( `' x " { 1o } ) )

  disjoint A x
  disjoint X x
  disjoint Y x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint X y
  disjoint Y y
  disjoint V x
  disjoint V y
  assert |- ( ( X e. ( 2o ^m A ) /\ Y e. A ) -> ( Y e. ( F ` X ) <-> ( X ` Y ) = 1o ) )

  proof
    cX
    c2o
    cA
    cmap
    co
    wcel
    #
    cY
    cA
    wcel
    #
    wa
    cY
    cX
    cF
    cfv
    #
    wcel
    #
    cY
    cX
    ccnv
    c1o
    csn
    cima
    #
    wcel
    #
    cY
    cX
    cfv
    c1o
    wceq
    #
    @0
    @3
    @5
    wb
    @1
    @0
    @2
    @4
    cY
    vx
    cA
    cF
    cX
    pw2f1o2.f
    pw2f1o2val
    eleq2d
    adantr
    @0
    @5
    @1
    @6
    @0
    cA
    c2o
    cX
    wf
    cX
    cA
    wfn
    @5
    @1
    @6
    wa
    wb
    cX
    c2o
    cA
    elmapi
    cA
    c2o
    cX
    ffn
    cA
    c1o
    cY
    cX
    fniniseg
    3syl
    baibd
    bitrd
end
