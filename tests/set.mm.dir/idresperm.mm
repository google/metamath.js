include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "f1oi.mm"
include "eqid.mm"
include "elsymgbas.mm"
include "mpbiri.mm"

theorem idresperm
  let cA: class A
  let cG: class G
  let cV: class V
  assume idresperm.g: |- G = ( SymGrp ` A )


  assert |- ( A e. V -> ( _I |` A ) e. ( Base ` G ) )

  proof
    cA
    cV
    wcel
    cid
    cA
    cres
    #
    cG
    cbs
    cfv
    #
    wcel
    cA
    cA
    @0
    wf1o
    cA
    f1oi
    cA
    @1
    @0
    cG
    cV
    idresperm.g
    @1
    eqid
    elsymgbas
    mpbiri
end
