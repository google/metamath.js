include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnp.mm"
include "csn.mm"
include "cdif.mm"
include "climc.mm"
include "crest.mm"
include "cnt.mm"
include "wbr.mm"
include "wfun.mm"
include "wb.mm"
include "dvfg.mm"
include "3ad2ant1.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "3syl.mm"
include "eqid.mm"
include "recnprss.mm"
include "simp2.mm"
include "simp3.mm"
include "eldv.mm"
include "bitrd.mm"
include "simplbda.mm"
include "sstrd.mm"
include "adantr.mm"
include "dvbss.mm"
include "sselda.mm"
include "wne.mm"
include "eldifsn.mm"
include "dvlem.mm"
include "sylan2br.mm"
include "limcmpt2.mm"
include "mpbid.mm"
include "syl5eqel.mm"

theorem dvcnp
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vy: setvar y
  assume dvcnp.j: |- J = ( K |`t A )
  assume dvcnp.k: |- K = ( TopOpen ` CCfld )
  assume dvcnp.g: |- G = ( z e. A |-> if ( z = B , ( ( S _D F ) ` B ) , ( ( ( F ` z ) - ( F ` B ) ) / ( z - B ) ) ) )

  disjoint A z
  disjoint B z
  disjoint F z
  disjoint K z
  disjoint S z
  disjoint J z
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint K y
  disjoint S y
  disjoint J y
  assert |- ( ( ( S e. { RR , CC } /\ F : A --> CC /\ A C_ S ) /\ B e. dom ( S _D F ) ) -> G e. ( ( J CnP K ) ` B ) )

  proof
    cS
    cr
    cc
    cpr
    wcel
    #
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    #
    w3a
    #
    cB
    cS
    cF
    cdv
    co
    #
    cdm
    #
    wcel
    #
    wa
    #
    cG
    vz
    cA
    vz
    cv
    #
    cB
    wceq
    cB
    @4
    cfv
    #
    @8
    cF
    cfv
    cB
    cF
    cfv
    cmin
    co
    @8
    cB
    cmin
    co
    cdiv
    co
    #
    cif
    cmpt
    #
    cB
    cJ
    cK
    ccnp
    co
    cfv
    #
    dvcnp.g
    @7
    @9
    vz
    cA
    cB
    csn
    cdif
    #
    @10
    cmpt
    #
    cB
    climc
    co
    wcel
    #
    @11
    @12
    wcel
    @3
    @6
    cB
    cA
    cK
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    wcel
    #
    @15
    @3
    @6
    cB
    @9
    @4
    wbr
    #
    @17
    @15
    wa
    @3
    @5
    cc
    @4
    wf
    #
    @4
    wfun
    @6
    @18
    wb
    @0
    @1
    @19
    @2
    cS
    cF
    dvfg
    3ad2ant1
    @5
    cc
    @4
    ffun
    cB
    @4
    funfvbrb
    3syl
    @3
    vz
    cA
    cB
    @9
    cS
    @16
    cF
    @14
    cK
    @16
    eqid
    dvcnp.k
    @14
    eqid
    @0
    @1
    cS
    cc
    wss
    @2
    cS
    recnprss
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    eldv
    bitrd
    simplbda
    @7
    vz
    cA
    cB
    @9
    @10
    cJ
    cK
    @3
    cA
    cc
    wss
    @6
    @3
    cA
    cS
    cc
    @22
    @20
    sstrd
    adantr
    #
    @3
    @5
    cA
    cB
    @3
    cA
    cS
    cF
    @20
    @21
    @22
    dvbss
    sselda
    #
    @8
    cA
    wcel
    @8
    cB
    wne
    wa
    @7
    @8
    @13
    wcel
    @10
    cc
    wcel
    @8
    cA
    cB
    eldifsn
    @7
    @8
    cB
    cA
    cF
    @3
    @1
    @6
    @21
    adantr
    @23
    @24
    dvlem
    sylan2br
    dvcnp.j
    dvcnp.k
    limcmpt2
    mpbid
    syl5eqel
end
