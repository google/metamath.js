include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "cstrset.mm"
include "setsval.mm"
include "df-strset.mm"
include "syl6reqr.mm"

theorem setsstrset
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( S e. V /\ B e. W ) -> [s B / A ]s S = ( S sSet <. ( A ` ndx ) , B >. ) )

  proof
    cS
    cV
    wcel
    cB
    cW
    wcel
    wa
    cS
    cnx
    cA
    cfv
    #
    cB
    cop
    #
    csts
    co
    cS
    cvv
    @0
    csn
    cdif
    cres
    @1
    csn
    cun
    cA
    cB
    cS
    cstrset
    @0
    cB
    cS
    cV
    cW
    setsval
    cA
    cB
    cS
    df-strset
    syl6reqr
end
