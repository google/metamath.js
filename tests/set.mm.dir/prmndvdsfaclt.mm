include "cprime.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "cfa.mm"
include "cfv.mm"
include "cdvds.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "prmnn.mm"
include "nnred.mm"
include "ltnle.mm"
include "syl2anr.mm"
include "wi.mm"
include "prmfac1.mm"
include "3exp.mm"
include "impcom.mm"
include "con3d.mm"
include "sylbid.mm"

theorem prmndvdsfaclt
  let cP: class P
  let cN: class N


  assert |- ( ( P e. Prime /\ N e. NN0 ) -> ( N < P -> -. P || ( ! ` N ) ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cP
    clt
    wbr
    #
    cP
    cN
    cle
    wbr
    #
    wn
    #
    cP
    cN
    cfa
    cfv
    cdvds
    wbr
    #
    wn
    @1
    cN
    cr
    wcel
    cP
    cr
    wcel
    @3
    @5
    wb
    @0
    cN
    nn0re
    @0
    cP
    cP
    prmnn
    nnred
    cN
    cP
    ltnle
    syl2anr
    @2
    @6
    @4
    @1
    @0
    @6
    @4
    wi
    @1
    @0
    @6
    @4
    cP
    cN
    prmfac1
    3exp
    impcom
    con3d
    sylbid
end
