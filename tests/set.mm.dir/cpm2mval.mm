include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "cpm2mfval.mm"
include "3adant3.mm"
include "oveq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "mpt2eq3dv.mm"
include "adantl.mm"
include "simp3.mm"
include "simp1.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "fvmptd.mm"

theorem cpm2mval
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume cpm2mfval.i: |- I = ( N cPolyMatToMat R )
  assume cpm2mfval.s: |- S = ( N ConstPolyMat R )

  disjoint N x
  disjoint N y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint M x
  disjoint M y
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint r x
  disjoint r y
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint V n
  disjoint V r
  disjoint M m
  disjoint V m
  assert |- ( ( N e. Fin /\ R e. V /\ M e. S ) -> ( I ` M ) = ( x e. N , y e. N |-> ( ( coe1 ` ( x M y ) ) ` 0 ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    cM
    cS
    wcel
    #
    w3a
    #
    vm
    cM
    vx
    vy
    cN
    cN
    cc0
    vx
    cv
    #
    vy
    cv
    #
    vm
    cv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    vx
    vy
    cN
    cN
    cc0
    @4
    @5
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    cS
    cI
    cvv
    @0
    @1
    cI
    vm
    cS
    @10
    cmpt
    wceq
    @2
    vx
    vy
    cR
    cS
    vm
    cI
    cN
    cV
    cpm2mfval.i
    cpm2mfval.s
    cpm2mfval
    3adant3
    @6
    cM
    wceq
    #
    @10
    @14
    wceq
    @3
    @15
    vx
    vy
    cN
    cN
    @9
    @13
    @15
    cc0
    @8
    @12
    @15
    @7
    @11
    cco1
    @4
    @5
    @6
    cM
    oveq
    fveq2d
    fveq1d
    mpt2eq3dv
    adantl
    @0
    @1
    @2
    simp3
    @3
    @0
    @0
    @14
    cvv
    wcel
    @0
    @1
    @2
    simp1
    #
    @16
    vx
    vy
    cN
    cN
    @13
    cfn
    cfn
    mpt2exga
    syl2anc
    fvmptd
end
