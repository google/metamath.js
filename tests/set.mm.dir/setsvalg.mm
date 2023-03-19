include "wcel.mm"
include "cvv.mm"
include "csts.mm"
include "co.mm"
include "csn.mm"
include "cdm.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "resexg.mm"
include "adantr.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "cv.mm"
include "simpl.mm"
include "simpr.mm"
include "sneqd.mm"
include "dmeqd.mm"
include "difeq2d.mm"
include "reseq12d.mm"
include "uneq12d.mm"
include "df-sets.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "syl2an.mm"

theorem setsvalg
  let cA: class A
  let cS: class S
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vs: setvar s
  let cB: class B


  assert |- ( ( S e. V /\ A e. W ) -> ( S sSet A ) = ( ( S |` ( _V \ dom { A } ) ) u. { A } ) )

  proof
    cS
    cV
    wcel
    cS
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    cS
    cA
    csts
    co
    cS
    cvv
    cA
    csn
    #
    cdm
    #
    cdif
    #
    cres
    #
    @2
    cun
    #
    wceq
    #
    cA
    cW
    wcel
    cS
    cV
    elex
    cA
    cW
    elex
    @0
    @1
    @6
    cvv
    wcel
    #
    @7
    @0
    @1
    wa
    @5
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @8
    @0
    @9
    @1
    cS
    @4
    cvv
    resexg
    adantr
    cA
    snex
    @5
    @2
    cvv
    cvv
    unexg
    sylancl
    vs
    ve
    cS
    cA
    cvv
    cvv
    vs
    cv
    #
    cvv
    ve
    cv
    #
    csn
    #
    cdm
    #
    cdif
    #
    cres
    #
    @12
    cun
    @6
    csts
    cvv
    @10
    cS
    wceq
    #
    @11
    cA
    wceq
    #
    wa
    #
    @15
    @5
    @12
    @2
    @18
    @10
    cS
    @14
    @4
    @16
    @17
    simpl
    @18
    @13
    @3
    cvv
    @18
    @12
    @2
    @18
    @11
    cA
    @16
    @17
    simpr
    sneqd
    #
    dmeqd
    difeq2d
    reseq12d
    @19
    uneq12d
    ve
    vs
    df-sets
    ovmpt2ga
    mpd3an3
    syl2an
end
