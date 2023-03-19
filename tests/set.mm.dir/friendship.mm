include "c3.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpl.mm"
include "friendshipgt3.mm"
include "syl3anc.mm"
include "ex.mm"
include "wn.mm"
include "c1.mm"
include "cle.mm"
include "wceq.mm"
include "ctp.mm"
include "w3o.mm"
include "wex.mm"
include "cn0.mm"
include "hashcl.mm"
include "simplr.mm"
include "hashge1.mm"
include "ad2ant2l.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "3re.mm"
include "lenlt.mm"
include "sylancl.mm"
include "biimprd.mm"
include "adantr.mm"
include "com12.mm"
include "impcom.mm"
include "3jca.mm"
include "exp31.mm"
include "mpcom.mm"
include "hash1to3.mm"
include "cvv.mm"
include "vex.mm"
include "eqid.mm"
include "1to3vfriendship.mm"
include "mpan.mm"
include "exlimiv.mm"
include "exlimivv.mm"
include "3syl.mm"
include "com14.mm"
include "3imp.mm"
include "pm2.61i.mm"

theorem friendship
  let vw: setvar w
  let vv: setvar v
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume friendship.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint G w
  disjoint v w
  disjoint V v
  disjoint V w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint a b
  disjoint a c
  disjoint a v
  disjoint a w
  disjoint b c
  disjoint b v
  disjoint b w
  disjoint c v
  disjoint c w
  disjoint V a
  disjoint V b
  disjoint V c
  assert |- ( ( G e. FriendGraph /\ V =/= (/) /\ V e. Fin ) -> E. v e. V A. w e. ( V \ { v } ) { v , w } e. ( Edg ` G ) )

  proof
    c3
    cV
    chash
    cfv
    #
    clt
    wbr
    #
    cG
    cfrgr
    wcel
    #
    cV
    c0
    wne
    #
    cV
    cfn
    wcel
    #
    w3a
    #
    vv
    cv
    #
    vw
    cv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vw
    cV
    @6
    csn
    cdif
    wral
    vv
    cV
    wrex
    #
    wi
    @1
    @5
    @8
    @1
    @5
    wa
    @2
    @4
    @1
    @8
    @1
    @2
    @3
    @4
    simpr1
    @1
    @2
    @3
    @4
    simpr3
    @1
    @5
    simpl
    vw
    vv
    cG
    cV
    friendship.v
    friendshipgt3
    syl3anc
    ex
    @5
    @1
    wn
    #
    @8
    @2
    @3
    @4
    @9
    @8
    wi
    @9
    @3
    @4
    @2
    @8
    @9
    @3
    @4
    @2
    @8
    wi
    #
    @9
    @3
    wa
    #
    @4
    wa
    @4
    c1
    @0
    cle
    wbr
    #
    @0
    c3
    cle
    wbr
    #
    w3a
    #
    cV
    va
    cv
    #
    csn
    wceq
    cV
    @15
    vb
    cv
    #
    cpr
    wceq
    cV
    @15
    @16
    vc
    cv
    #
    ctp
    wceq
    w3o
    #
    vc
    wex
    #
    vb
    wex
    va
    wex
    @10
    @4
    @11
    @14
    @0
    cn0
    wcel
    #
    @4
    @11
    @14
    wi
    cV
    hashcl
    @20
    @4
    @11
    @14
    @20
    @4
    wa
    #
    @11
    wa
    @4
    @12
    @13
    @20
    @4
    @11
    simplr
    @4
    @3
    @12
    @20
    @9
    cV
    cfn
    hashge1
    ad2ant2l
    @11
    @21
    @13
    @9
    @21
    @13
    wi
    @3
    @21
    @9
    @13
    @20
    @9
    @13
    wi
    @4
    @20
    @13
    @9
    @20
    @0
    cr
    wcel
    c3
    cr
    wcel
    @13
    @9
    wb
    @0
    nn0re
    3re
    @0
    c3
    lenlt
    sylancl
    biimprd
    adantr
    com12
    adantr
    impcom
    3jca
    exp31
    mpcom
    impcom
    cV
    va
    vb
    vc
    hash1to3
    @19
    @10
    va
    vb
    @18
    @10
    vc
    @15
    cvv
    wcel
    @18
    @10
    va
    vex
    vw
    vv
    @15
    @16
    @17
    @7
    cG
    cV
    cvv
    friendship.v
    @7
    eqid
    1to3vfriendship
    mpan
    exlimiv
    exlimivv
    3syl
    exp31
    com14
    3imp
    com12
    pm2.61i
end
