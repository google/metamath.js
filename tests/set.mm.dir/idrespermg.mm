include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "csn.mm"
include "csubg.mm"
include "cfv.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "wa.mm"
include "idressubgsymg.mm"
include "cress.mm"
include "co.mm"
include "eqid.mm"
include "pgrpsubgsymgbi.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "ressbas.mm"
include "mp1i.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "anim12ci.mm"
include "ex.mm"
include "sylbid.mm"
include "mpd.mm"

theorem idrespermg
  let cA: class A
  let cE: class E
  let cG: class G
  let cV: class V
  assume idresperm.g: |- G = ( SymGrp ` A )
  assume idrespermg.e: |- E = ( G |`s { ( _I |` A ) } )


  assert |- ( A e. V -> ( E e. Grp /\ ( Base ` E ) C_ ( Base ` G ) ) )

  proof
    cA
    cV
    wcel
    #
    cid
    cA
    cres
    #
    csn
    #
    cG
    csubg
    cfv
    wcel
    #
    cE
    cgrp
    wcel
    #
    cE
    cbs
    cfv
    #
    cG
    cbs
    cfv
    #
    wss
    #
    wa
    #
    cA
    cG
    cV
    idresperm.g
    idressubgsymg
    @0
    @3
    @2
    @6
    wss
    #
    cG
    @2
    cress
    co
    #
    cgrp
    wcel
    #
    wa
    #
    @8
    cA
    @6
    @2
    cG
    cV
    idresperm.g
    @6
    eqid
    #
    pgrpsubgsymgbi
    @0
    @12
    @8
    @0
    @7
    @12
    @4
    @0
    @5
    @2
    @6
    cin
    #
    @6
    @2
    cvv
    wcel
    @14
    @5
    wceq
    @0
    @1
    snex
    @2
    @6
    cE
    cvv
    cG
    idrespermg.e
    @13
    ressbas
    mp1i
    @2
    @6
    inss2
    syl6eqssr
    @11
    @4
    @9
    @11
    @4
    @10
    cE
    cgrp
    cE
    @10
    idrespermg.e
    eqcomi
    eleq1i
    biimpi
    adantl
    anim12ci
    ex
    sylbid
    mpd
end
