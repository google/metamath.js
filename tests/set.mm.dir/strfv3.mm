include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "strfv.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "syl6reqr.mm"

theorem strfv3
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cV: class V
  let cX: class X
  assume strfv3.u: |- ( ph -> U = S )
  assume strfv3.s: |- S Struct X
  assume strfv3.e: |- E = Slot ( E ` ndx )
  assume strfv3.n: |- { <. ( E ` ndx ) , C >. } C_ S
  assume strfv3.c: |- ( ph -> C e. V )
  assume strfv3.a: |- A = ( E ` U )


  assert |- ( ph -> A = C )

  proof
    wph
    cC
    cU
    cE
    cfv
    #
    cA
    wph
    cC
    cS
    cE
    cfv
    #
    @0
    wph
    cC
    cV
    wcel
    cC
    @1
    wceq
    strfv3.c
    cC
    cS
    cE
    cV
    cX
    strfv3.s
    strfv3.e
    strfv3.n
    strfv
    syl
    wph
    cU
    cS
    cE
    strfv3.u
    fveq2d
    eqtr4d
    strfv3.a
    syl6reqr
end
