include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "mul0or.mm"
include "syl2anc.mm"
include "oridm.mm"
include "syl6bb.mm"

theorem msq0d
  let wph: wff ph
  let cA: class A
  assume msq0d.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( A x. A ) = 0 <-> A = 0 ) )

  proof
    wph
    cA
    cA
    cmul
    co
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    @1
    wo
    #
    @1
    wph
    cA
    cc
    wcel
    #
    @3
    @0
    @2
    wb
    msq0d.1
    msq0d.1
    cA
    cA
    mul0or
    syl2anc
    @1
    oridm
    syl6bb
end
