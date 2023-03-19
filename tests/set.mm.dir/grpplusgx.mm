include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cop.mm"
include "c2.mm"
include "cpr.mm"
include "cnx.mm"
include "cbs.mm"
include "basendx.mm"
include "opeq1i.mm"
include "plusgndx.mm"
include "preq12i.mm"
include "eqtr4i.mm"
include "grpplusg.mm"
include "ax-mp.mm"

theorem grpplusgx
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume grpstrx.b: |- B e. _V
  assume grpstrx.p: |- .+ e. _V
  assume grpstrx.g: |- G = { <. 1 , B >. , <. 2 , .+ >. }


  assert |- .+ = ( +g ` G )

  proof
    c.pl
    cvv
    wcel
    c.pl
    cG
    cplusg
    cfv
    wceq
    grpstrx.p
    cB
    c.pl
    cG
    cvv
    cG
    c1
    cB
    cop
    #
    c2
    c.pl
    cop
    #
    cpr
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cpr
    grpstrx.g
    @3
    @0
    @5
    @1
    @2
    c1
    cB
    basendx
    opeq1i
    @4
    c2
    c.pl
    plusgndx
    opeq1i
    preq12i
    eqtr4i
    grpplusg
    ax-mp
end
