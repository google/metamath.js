include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ccom.mm"
include "symgov.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "f1oco.mm"
include "syl2an.mm"
include "cvv.mm"
include "wb.mm"
include "coexg.mm"
include "elsymgbas2.mm"
include "syl.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem symgcl
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume symgplusg.1: |- G = ( SymGrp ` A )
  assume symgplusg.2: |- B = ( Base ` G )
  assume symgplusg.3: |- .+ = ( +g ` G )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .+ Y ) e. B )

  proof
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    c.pl
    co
    cX
    cY
    ccom
    #
    cB
    cA
    cB
    c.pl
    cG
    cX
    cY
    symgplusg.1
    symgplusg.2
    symgplusg.3
    symgov
    @2
    @3
    cB
    wcel
    #
    cA
    cA
    @3
    wf1o
    #
    @0
    cA
    cA
    cX
    wf1o
    cA
    cA
    cY
    wf1o
    @5
    @1
    cA
    cB
    cX
    cG
    symgplusg.1
    symgplusg.2
    symgbasf1o
    cA
    cB
    cY
    cG
    symgplusg.1
    symgplusg.2
    symgbasf1o
    cA
    cA
    cA
    cX
    cY
    f1oco
    syl2an
    @2
    @3
    cvv
    wcel
    @4
    @5
    wb
    cX
    cY
    cB
    cB
    coexg
    cA
    cB
    @3
    cG
    cvv
    symgplusg.1
    symgplusg.2
    elsymgbas2
    syl
    mpbird
    eqeltrd
end
