include "wcel.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cdm.mm"
include "cun.mm"
include "wceq.mm"
include "opex.mm"
include "setsvalg.mm"
include "mpan2.mm"
include "reseq1d.mm"
include "resundir.mm"
include "c0.mm"
include "wss.mm"
include "dmsnopss.mm"
include "sscon.mm"
include "ax-mp.mm"
include "resabs1.mm"
include "cin.mm"
include "dmres.mm"
include "disj2.mm"
include "mpbir.mm"
include "eqtri.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "reldm0.mm"
include "uneq12i.mm"
include "un0.mm"
include "syl6eq.mm"

theorem setsres
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( ( S sSet <. A , B >. ) |` ( _V \ { A } ) ) = ( S |` ( _V \ { A } ) ) )

  proof
    cS
    cV
    wcel
    #
    cS
    cA
    cB
    cop
    #
    csts
    co
    #
    cvv
    cA
    csn
    #
    cdif
    #
    cres
    cS
    cvv
    @1
    csn
    #
    cdm
    #
    cdif
    #
    cres
    #
    @5
    cun
    #
    @4
    cres
    #
    cS
    @4
    cres
    #
    @0
    @2
    @9
    @4
    @0
    @1
    cvv
    wcel
    @2
    @9
    wceq
    cA
    cB
    opex
    @1
    cS
    cV
    cvv
    setsvalg
    mpan2
    reseq1d
    @10
    @8
    @4
    cres
    #
    @5
    @4
    cres
    #
    cun
    #
    @11
    @8
    @5
    @4
    resundir
    @14
    @11
    c0
    cun
    @11
    @12
    @11
    @13
    c0
    @4
    @7
    wss
    #
    @12
    @11
    wceq
    @6
    @3
    wss
    @15
    cA
    cB
    dmsnopss
    @6
    @3
    cvv
    sscon
    ax-mp
    #
    cS
    @4
    @7
    resabs1
    ax-mp
    @13
    c0
    wceq
    #
    @13
    cdm
    #
    c0
    wceq
    #
    @18
    @4
    @6
    cin
    #
    c0
    @5
    @4
    dmres
    @20
    c0
    wceq
    @15
    @16
    @4
    @6
    disj2
    mpbir
    eqtri
    @13
    wrel
    @17
    @19
    wb
    @5
    @4
    relres
    @13
    reldm0
    ax-mp
    mpbir
    uneq12i
    @11
    un0
    eqtri
    eqtri
    syl6eq
end
