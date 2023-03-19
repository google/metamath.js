include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cpr.mm"
include "c1.mm"
include "cstr.mm"
include "1nn.mm"
include "basendx.mm"
include "ndxarg.mm"
include "strle2.mm"
include "eqbrtri.mm"

theorem 2strstr
  let cB: class B
  let c.pl: class .+
  let cE: class E
  let cG: class G
  let cN: class N
  assume 2str.g: |- G = { <. ( Base ` ndx ) , B >. , <. ( E ` ndx ) , .+ >. }
  assume 2str.e: |- E = Slot N
  assume 2str.l: |- 1 < N
  assume 2str.n: |- N e. NN


  assert |- G Struct <. 1 , N >.

  proof
    cG
    cnx
    cbs
    cfv
    #
    cB
    cop
    cnx
    cE
    cfv
    #
    c.pl
    cop
    cpr
    c1
    cN
    cop
    cstr
    2str.g
    @0
    @1
    c1
    cN
    cB
    c.pl
    1nn
    basendx
    2str.l
    2str.n
    cE
    cN
    2str.e
    2str.n
    ndxarg
    strle2
    eqbrtri
end
