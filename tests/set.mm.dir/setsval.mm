include "wcel.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdm.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "opex.mm"
include "setsvalg.mm"
include "mpan2.mm"
include "dmsnopg.mm"
include "difeq2d.mm"
include "reseq2d.mm"
include "uneq1d.mm"
include "sylan9eq.mm"

theorem setsval
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vs: setvar s


  assert |- ( ( S e. V /\ B e. W ) -> ( S sSet <. A , B >. ) = ( ( S |` ( _V \ { A } ) ) u. { <. A , B >. } ) )

  proof
    cS
    cV
    wcel
    #
    cB
    cW
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
    cS
    cvv
    @2
    csn
    #
    cdm
    #
    cdif
    #
    cres
    #
    @4
    cun
    #
    cS
    cvv
    cA
    csn
    #
    cdif
    #
    cres
    #
    @4
    cun
    @0
    @2
    cvv
    wcel
    @3
    @8
    wceq
    cA
    cB
    opex
    @2
    cS
    cV
    cvv
    setsvalg
    mpan2
    @1
    @7
    @11
    @4
    @1
    @6
    @10
    cS
    @1
    @5
    @9
    cvv
    cA
    cB
    cW
    dmsnopg
    difeq2d
    reseq2d
    uneq1d
    sylan9eq
end
