include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ispsubclN.mm"
include "biimpa.mm"

theorem psubcliN
  let cA: class A
  let cC: class C
  let cD: class D
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let vk: setvar k
  let vs: setvar s
  let vx: setvar x
  assume psubclset.a: |- A = ( Atoms ` K )
  assume psubclset.p: |- ._|_ = ( _|_P ` K )
  assume psubclset.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. D /\ X e. C ) -> ( X C_ A /\ ( ._|_ ` ( ._|_ ` X ) ) = X ) )

  proof
    cK
    cD
    wcel
    cX
    cC
    wcel
    cX
    cA
    wss
    cX
    c.pe
    cfv
    c.pe
    cfv
    cX
    wceq
    wa
    cA
    cC
    cD
    cK
    c.pe
    cX
    psubclset.a
    psubclset.p
    psubclset.c
    ispsubclN
    biimpa
end
