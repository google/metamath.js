include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "syl6eleq.mm"
include "matecl.mm"
include "syl3anc.mm"

theorem matecld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume matecl.a: |- A = ( N Mat R )
  assume matecl.k: |- K = ( Base ` R )
  assume matecld.b: |- B = ( Base ` A )
  assume matecld.i: |- ( ph -> I e. N )
  assume matecld.j: |- ( ph -> J e. N )
  assume matecld.m: |- ( ph -> M e. B )


  assert |- ( ph -> ( I M J ) e. K )

  proof
    wph
    cI
    cN
    wcel
    cJ
    cN
    wcel
    cM
    cA
    cbs
    cfv
    #
    wcel
    cI
    cJ
    cM
    co
    cK
    wcel
    matecld.i
    matecld.j
    wph
    cM
    cB
    @0
    matecld.m
    matecld.b
    syl6eleq
    cA
    cR
    cI
    cJ
    cK
    cM
    cN
    matecl.a
    matecl.k
    matecl
    syl3anc
end
