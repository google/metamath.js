include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cpm2mval.mm"
include "adantr.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem cpm2mvalel
  let cR: class R
  let cS: class S
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume cpm2mfval.i: |- I = ( N cPolyMatToMat R )
  assume cpm2mfval.s: |- S = ( N ConstPolyMat R )


  assert |- ( ( ( N e. Fin /\ R e. V /\ M e. S ) /\ ( X e. N /\ Y e. N ) ) -> ( X ( I ` M ) Y ) = ( ( coe1 ` ( X M Y ) ) ` 0 ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    cM
    cS
    wcel
    w3a
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    cX
    cY
    cN
    cN
    cc0
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cc0
    cX
    cY
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cM
    cI
    cfv
    #
    cvv
    @0
    @13
    vx
    vy
    cN
    cN
    @9
    cmpt2
    wceq
    @3
    vx
    vy
    cR
    cS
    cI
    cM
    cN
    cV
    cpm2mfval.i
    cpm2mfval.s
    cpm2mval
    adantr
    @5
    cX
    wceq
    @6
    cY
    wceq
    wa
    #
    @9
    @12
    wceq
    @4
    @14
    cc0
    @8
    @11
    @14
    @7
    @10
    cco1
    @5
    cX
    @6
    cY
    cM
    oveq12
    fveq2d
    fveq1d
    adantl
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    @4
    cc0
    @11
    fvexd
    ovmpt2d
end
