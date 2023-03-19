include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "wtru.mm"
include "cxr.mm"
include "ledm.mm"
include "ctsr.mm"
include "wcel.mm"
include "letsr.mm"
include "a1i.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "cicc.mm"
include "sseli.mm"
include "iccval.mm"
include "syl2an.mm"
include "eqsstr3d.mm"
include "adantl.mm"
include "ordtrest2.mm"
include "eqcomd.mm"
include "trud.mm"

theorem ordtrestixx
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vz: setvar z
  assume ordtrestixx.1: |- A C_ RR*
  assume ordtrestixx.2: |- ( ( x e. A /\ y e. A ) -> ( x [,] y ) C_ A )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( ordTop ` <_ ) |`t A ) = ( ordTop ` ( <_ i^i ( A X. A ) ) )

  proof
    cle
    cordt
    cfv
    cA
    crest
    co
    #
    cle
    cA
    cA
    cxp
    cin
    cordt
    cfv
    #
    wceq
    wtru
    @1
    @0
    wtru
    vx
    vy
    vz
    cA
    cle
    cxr
    ledm
    cle
    ctsr
    wcel
    wtru
    letsr
    a1i
    cA
    cxr
    wss
    wtru
    ordtrestixx.1
    a1i
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @2
    vz
    cv
    #
    cle
    wbr
    @7
    @4
    cle
    wbr
    wa
    vz
    cxr
    crab
    #
    cA
    wss
    wtru
    @6
    @8
    @2
    @4
    cicc
    co
    #
    cA
    @3
    @2
    cxr
    wcel
    @4
    cxr
    wcel
    @9
    @8
    wceq
    @5
    cA
    cxr
    @2
    ordtrestixx.1
    sseli
    cA
    cxr
    @4
    ordtrestixx.1
    sseli
    vz
    @2
    @4
    iccval
    syl2an
    ordtrestixx.2
    eqsstr3d
    adantl
    ordtrest2
    eqcomd
    trud
end
