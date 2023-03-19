include "wcel.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wel.mm"
include "c1o.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "pw2f1ocnv.mm"
include "simpld.mm"

theorem pw2f1o2
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume pw2f1o2.f: |- F = ( x e. ( 2o ^m A ) |-> ( `' x " { 1o } ) )

  disjoint A x
  disjoint V x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint V y
  assert |- ( A e. V -> F : ( 2o ^m A ) -1-1-onto-> ~P A )

  proof
    cA
    cV
    wcel
    c2o
    cA
    cmap
    co
    cA
    cpw
    #
    cF
    wf1o
    cF
    ccnv
    vy
    @0
    vz
    cA
    vz
    vy
    wel
    c1o
    c0
    cif
    cmpt
    cmpt
    wceq
    vx
    vy
    vz
    cA
    cF
    cV
    pw2f1o2.f
    pw2f1ocnv
    simpld
end
