include "ccrg.mm"
include "wcel.mm"
include "mdetf.mm"
include "ffvelrnda.mm"

theorem mdetcl
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cK: class K
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vc: setvar c
  let vm: setvar m
  assume mdetf.d: |- D = ( N maDet R )
  assume mdetf.a: |- A = ( N Mat R )
  assume mdetf.b: |- B = ( Base ` A )
  assume mdetf.k: |- K = ( Base ` R )


  assert |- ( ( R e. CRing /\ M e. B ) -> ( D ` M ) e. K )

  proof
    cR
    ccrg
    wcel
    cB
    cK
    cM
    cD
    cA
    cB
    cD
    cR
    cK
    cN
    mdetf.d
    mdetf.a
    mdetf.b
    mdetf.k
    mdetf
    ffvelrnda
end
