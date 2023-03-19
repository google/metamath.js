include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "wf1.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "simpl.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "mp1i.mm"
include "wss.mm"
include "wceq.mm"
include "inss2.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "ctopon.mm"
include "cfv.mm"
include "ctop.mm"
include "adantr.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "idcn.mm"
include "syl.mm"
include "cnrest.mm"
include "sylancl.mm"
include "syl5eqelr.mm"
include "restin.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "syl3anc.mm"

theorem resthauslem
  let cA: class A
  let cS: class S
  let cJ: class J
  let cV: class V
  assume resthauslem.1: |- ( J e. A -> J e. Top )
  assume resthauslem.2: |- ( ( J e. A /\ ( _I |` ( S i^i U. J ) ) : ( S i^i U. J ) -1-1-> ( S i^i U. J ) /\ ( _I |` ( S i^i U. J ) ) e. ( ( J |`t S ) Cn J ) ) -> ( J |`t S ) e. A )


  assert |- ( ( J e. A /\ S e. V ) -> ( J |`t S ) e. A )

  proof
    cJ
    cA
    wcel
    #
    cS
    cV
    wcel
    #
    wa
    #
    @0
    cS
    cJ
    cuni
    #
    cin
    #
    @4
    cid
    @4
    cres
    #
    wf1
    #
    @5
    cJ
    cS
    crest
    co
    #
    cJ
    ccn
    co
    #
    wcel
    @7
    cA
    wcel
    @0
    @1
    simpl
    @4
    @4
    @5
    wf1o
    @6
    @2
    @4
    f1oi
    @4
    @4
    @5
    f1of1
    mp1i
    @2
    @5
    cJ
    @4
    crest
    co
    #
    cJ
    ccn
    co
    #
    @8
    @2
    @5
    cid
    @3
    cres
    #
    @4
    cres
    #
    @10
    @4
    @3
    wss
    #
    @12
    @5
    wceq
    cS
    @3
    inss2
    #
    cid
    @4
    @3
    resabs1
    ax-mp
    @2
    @11
    cJ
    cJ
    ccn
    co
    wcel
    #
    @13
    @12
    @10
    wcel
    @2
    cJ
    @3
    ctopon
    cfv
    wcel
    #
    @15
    @2
    cJ
    ctop
    wcel
    #
    @16
    @0
    @17
    @1
    resthauslem.1
    adantr
    cJ
    @3
    @3
    eqid
    #
    toptopon
    sylib
    cJ
    @3
    idcn
    syl
    @14
    @4
    @11
    cJ
    cJ
    @3
    @18
    cnrest
    sylancl
    syl5eqelr
    @2
    @7
    @9
    cJ
    ccn
    cS
    cJ
    cA
    cV
    @3
    @18
    restin
    oveq1d
    eleqtrrd
    resthauslem.2
    syl3anc
end
