include "c1.mm"
include "cop.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cstr.mm"
include "cslot.mm"
include "cpr.mm"
include "eqid.mm"
include "ndxarg.mm"
include "eqcomi.mm"
include "opeq1i.mm"
include "preq2i.mm"
include "eqtri.mm"
include "clt.mm"
include "basendx.mm"
include "eqbrtrri.mm"
include "2strstr.mm"
include "breqtrri.mm"

theorem 2strstr1
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  assume 2str1.g: |- G = { <. ( Base ` ndx ) , B >. , <. N , .+ >. }
  assume 2str1.b: |- ( Base ` ndx ) < N
  assume 2str1.n: |- N e. NN


  assert |- G Struct <. ( Base ` ndx ) , N >.

  proof
    cG
    c1
    cN
    cop
    cnx
    cbs
    cfv
    #
    cN
    cop
    cstr
    cB
    c.pl
    cN
    cslot
    #
    cG
    cN
    cG
    @0
    cB
    cop
    #
    cN
    c.pl
    cop
    #
    cpr
    @2
    cnx
    @1
    cfv
    #
    c.pl
    cop
    #
    cpr
    2str1.g
    @3
    @5
    @2
    cN
    @4
    c.pl
    @4
    cN
    @1
    cN
    @1
    eqid
    #
    2str1.n
    ndxarg
    eqcomi
    opeq1i
    preq2i
    eqtri
    @6
    @0
    c1
    cN
    clt
    basendx
    2str1.b
    eqbrtrri
    2str1.n
    2strstr
    @0
    c1
    cN
    basendx
    opeq1i
    breqtrri
end
