include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "eqid.mm"
include "limsupequzmptlem.mm"

theorem limsupequzmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  assume limsupequzmpt.j: |- F/ j ph
  assume limsupequzmpt.m: |- ( ph -> M e. ZZ )
  assume limsupequzmpt.n: |- ( ph -> N e. ZZ )
  assume limsupequzmpt.a: |- A = ( ZZ>= ` M )
  assume limsupequzmpt.b: |- B = ( ZZ>= ` N )
  assume limsupequzmpt.c: |- ( ( ph /\ j e. A ) -> C e. V )
  assume limsupequzmpt.d: |- ( ( ph /\ j e. B ) -> C e. W )

  disjoint A j
  disjoint B j
  disjoint M j
  disjoint N j
  assert |- ( ph -> ( limsup ` ( j e. A |-> C ) ) = ( limsup ` ( j e. B |-> C ) ) )

  proof
    wph
    cA
    cB
    cC
    vj
    cM
    cN
    cle
    wbr
    cN
    cM
    cif
    #
    cM
    cN
    cV
    cW
    limsupequzmpt.j
    limsupequzmpt.m
    limsupequzmpt.n
    limsupequzmpt.a
    limsupequzmpt.b
    limsupequzmpt.c
    limsupequzmpt.d
    @0
    eqid
    limsupequzmptlem
end
