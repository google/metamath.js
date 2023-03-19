include "c1.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "crab.mm"
include "cr.mm"
include "cinf.mm"
include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "cpellfund.mm"
include "wceq.mm"
include "fveq2.mm"
include "rabeq.mm"
include "syl.mm"
include "infeq1d.mm"
include "df-pellfund.mm"
include "ltso.mm"
include "infex.mm"
include "fvmpt.mm"

theorem pellfundval
  let vx: setvar x
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A

  disjoint D x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint A d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  assert |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) = inf ( { x e. ( Pell14QR ` D ) | 1 < x } , RR , < ) )

  proof
    va
    cD
    c1
    vx
    cv
    clt
    wbr
    #
    vx
    va
    cv
    #
    cpell14qr
    cfv
    #
    crab
    #
    cr
    clt
    cinf
    @0
    vx
    cD
    cpell14qr
    cfv
    #
    crab
    #
    cr
    clt
    cinf
    cn
    csquarenn
    cdif
    cpellfund
    @1
    cD
    wceq
    #
    cr
    @3
    @5
    clt
    @6
    @2
    @4
    wceq
    @3
    @5
    wceq
    @1
    cD
    cpell14qr
    fveq2
    @0
    vx
    @2
    @4
    rabeq
    syl
    infeq1d
    va
    vx
    df-pellfund
    cr
    @5
    clt
    ltso
    infex
    fvmpt
end
