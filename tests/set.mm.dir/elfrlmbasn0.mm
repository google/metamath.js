include "wcel.mm"
include "wf.mm"
include "c0.mm"
include "wne.mm"
include "frlmbasf.mm"
include "ex.mm"
include "wceq.mm"
include "f0dom0.mm"
include "biimprd.mm"
include "necon3d.mm"
include "com12.mm"
include "sylan9.mm"

theorem elfrlmbasn0
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let va: setvar a
  assume frlmfibas.f: |- F = ( R freeLMod I )
  assume frlmfibas.n: |- N = ( Base ` R )
  assume elfrlmbasn0.b: |- B = ( Base ` F )


  assert |- ( ( I e. V /\ I =/= (/) ) -> ( X e. B -> X =/= (/) ) )

  proof
    cI
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    cI
    cN
    cX
    wf
    #
    cI
    c0
    wne
    #
    cX
    c0
    wne
    #
    @0
    @1
    @2
    cB
    cR
    cF
    cI
    cN
    cV
    cX
    frlmfibas.f
    frlmfibas.n
    elfrlmbasn0.b
    frlmbasf
    ex
    @2
    @3
    @4
    @2
    cX
    c0
    cI
    c0
    @2
    cI
    c0
    wceq
    cX
    c0
    wceq
    cX
    cI
    cN
    f0dom0
    biimprd
    necon3d
    com12
    sylan9
end
