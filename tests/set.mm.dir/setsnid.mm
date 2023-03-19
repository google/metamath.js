include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "wceq.mm"
include "cnx.mm"
include "id.mm"
include "strfvnd.mm"
include "ovex.mm"
include "strfvn.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "setsres.mm"
include "fveq1d.mm"
include "wne.mm"
include "fvex.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "fvres.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "reldmsets.mm"
include "ovprc1.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem setsnid
  let cC: class C
  let cD: class D
  let cE: class E
  let cW: class W
  assume setsid.e: |- E = Slot ( E ` ndx )
  assume setsnid.n: |- ( E ` ndx ) =/= D


  assert |- ( E ` W ) = ( E ` ( W sSet <. D , C >. ) )

  proof
    cW
    cvv
    wcel
    #
    cW
    cE
    cfv
    #
    cW
    cD
    cC
    cop
    #
    csts
    co
    #
    cE
    cfv
    #
    wceq
    @0
    @1
    cnx
    cE
    cfv
    #
    cW
    cfv
    #
    @4
    @0
    cW
    cE
    @5
    cvv
    setsid.e
    @0
    id
    strfvnd
    @0
    @4
    @5
    @3
    cfv
    #
    @6
    @3
    cE
    @5
    cW
    @2
    csts
    ovex
    setsid.e
    strfvn
    @0
    @5
    @3
    cvv
    cD
    csn
    cdif
    #
    cres
    #
    cfv
    #
    @5
    cW
    @8
    cres
    #
    cfv
    #
    @7
    @6
    @0
    @5
    @9
    @11
    cD
    cC
    cW
    cvv
    setsres
    fveq1d
    @5
    @8
    wcel
    #
    @10
    @7
    wceq
    @13
    @5
    cvv
    wcel
    @5
    cD
    wne
    cnx
    cE
    fvex
    setsnid.n
    @5
    cvv
    cD
    eldifsn
    mpbir2an
    #
    @5
    @8
    @3
    fvres
    ax-mp
    @13
    @12
    @6
    wceq
    @14
    @5
    @8
    cW
    fvres
    ax-mp
    3eqtr3g
    syl5eq
    eqtr4d
    @0
    wn
    #
    c0
    c0
    cE
    cfv
    @1
    @4
    cE
    @5
    setsid.e
    str0
    cW
    cE
    fvprc
    @15
    @3
    c0
    cE
    cW
    @2
    csts
    reldmsets
    ovprc1
    fveq2d
    3eqtr4a
    pm2.61i
end
