include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cdm.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "opex.mm"
include "a1i.mm"
include "setsvalg.mm"
include "sylan2.mm"
include "dmeqd.mm"
include "dmun.mm"
include "cin.mm"
include "dmres.mm"
include "dmsnopg.mm"
include "adantl.mm"
include "difeq2d.mm"
include "ineq1d.mm"
include "incom.mm"
include "invdif.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "uneq12d.mm"
include "undif1.mm"
include "3eqtrd.mm"

theorem setsdm
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( G e. V /\ E e. W ) -> dom ( G sSet <. I , E >. ) = ( dom G u. { I } ) )

  proof
    cG
    cV
    wcel
    #
    cE
    cW
    wcel
    #
    wa
    #
    cG
    cI
    cE
    cop
    #
    csts
    co
    #
    cdm
    cG
    cvv
    @3
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
    cdm
    #
    cG
    cdm
    #
    cI
    csn
    #
    cdif
    #
    @12
    cun
    #
    @11
    @12
    cun
    #
    @2
    @4
    @9
    @1
    @0
    @3
    cvv
    wcel
    #
    @4
    @9
    wceq
    @16
    @1
    cI
    cE
    opex
    a1i
    @3
    cG
    cV
    cvv
    setsvalg
    sylan2
    dmeqd
    @2
    @10
    @8
    cdm
    #
    @6
    cun
    @14
    @8
    @5
    dmun
    @2
    @17
    @13
    @6
    @12
    @2
    @17
    @7
    @11
    cin
    #
    @13
    cG
    @7
    dmres
    @2
    @18
    cvv
    @12
    cdif
    #
    @11
    cin
    #
    @13
    @2
    @7
    @19
    @11
    @2
    @6
    @12
    cvv
    @1
    @6
    @12
    wceq
    @0
    cI
    cE
    cW
    dmsnopg
    adantl
    #
    difeq2d
    ineq1d
    @20
    @11
    @19
    cin
    @13
    @19
    @11
    incom
    @11
    @12
    invdif
    eqtri
    syl6eq
    syl5eq
    @21
    uneq12d
    syl5eq
    @14
    @15
    wceq
    @2
    @11
    @12
    undif1
    a1i
    3eqtrd
end
