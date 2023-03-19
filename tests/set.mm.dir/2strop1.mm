include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "2strstr1.mm"
include "ndxid.mm"
include "csn.mm"
include "cpr.mm"
include "snsspr2.mm"
include "ndxarg.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "3sstr4i.mm"
include "strfv.mm"

theorem 2strop1
  let cB: class B
  let c.pl: class .+
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  assume 2str1.g: |- G = { <. ( Base ` ndx ) , B >. , <. N , .+ >. }
  assume 2str1.b: |- ( Base ` ndx ) < N
  assume 2str1.n: |- N e. NN
  assume 2str1.e: |- E = Slot N


  assert |- ( .+ e. V -> .+ = ( E ` G ) )

  proof
    c.pl
    cG
    cE
    cV
    cnx
    cbs
    cfv
    #
    cN
    cop
    cB
    c.pl
    cG
    cN
    2str1.g
    2str1.b
    2str1.n
    2strstr1
    cE
    cN
    2str1.e
    2str1.n
    ndxid
    cN
    c.pl
    cop
    #
    csn
    @0
    cB
    cop
    #
    @1
    cpr
    cnx
    cE
    cfv
    #
    c.pl
    cop
    #
    csn
    cG
    @2
    @1
    snsspr2
    @4
    @1
    @3
    cN
    c.pl
    cE
    cN
    2str1.e
    2str1.n
    ndxarg
    opeq1i
    sneqi
    2str1.g
    3sstr4i
    strfv
end
