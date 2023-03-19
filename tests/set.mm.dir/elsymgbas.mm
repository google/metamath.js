include "wcel.mm"
include "cvv.mm"
include "wf1o.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "wf.mm"
include "f1of.mm"
include "fex.mm"
include "expcom.mm"
include "syl5.mm"
include "wb.mm"
include "elsymgbas2.mm"
include "pm5.21ndd.mm"

theorem elsymgbas
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( A e. V -> ( F e. B <-> F : A -1-1-onto-> A ) )

  proof
    cA
    cV
    wcel
    #
    cF
    cvv
    wcel
    #
    cF
    cB
    wcel
    #
    cA
    cA
    cF
    wf1o
    #
    @2
    @1
    wi
    @0
    cF
    cB
    elex
    a1i
    @3
    cA
    cA
    cF
    wf
    #
    @0
    @1
    cA
    cA
    cF
    f1of
    @4
    @0
    @1
    cA
    cA
    cV
    cF
    fex
    expcom
    syl5
    @1
    @2
    @3
    wb
    wi
    @0
    cA
    cB
    cF
    cG
    cvv
    symgbas.1
    symgbas.2
    elsymgbas2
    a1i
    pm5.21ndd
end
