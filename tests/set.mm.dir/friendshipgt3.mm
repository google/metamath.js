include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c3.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cvtxdg.mm"
include "wceq.mm"
include "wrex.mm"
include "crusgr.mm"
include "cpr.mm"
include "cedg.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wo.mm"
include "wi.mm"
include "cn0.mm"
include "wn.mm"
include "eqid.mm"
include "frgrregorufrg.mm"
include "3ad2ant1.mm"
include "frgrogt3nreg.mm"
include "cfusgr.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "anim1i.mm"
include "isfusgr.mm"
include "sylibr.mm"
include "3adant3.mm"
include "cc0.mm"
include "0red.mm"
include "cr.mm"
include "3re.mm"
include "a1i.mm"
include "hashcl.mm"
include "nn0red.mm"
include "adantr.mm"
include "3pos.mm"
include "simpr.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "wb.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "3adant1.mm"
include "fusgrn0degnn0.mm"
include "syl2anc.mm"
include "r19.26.mm"
include "simpllr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ad4ant13.mm"
include "ornld.mm"
include "syl.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "breq2.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "adantl.mm"
include "mpbird.mm"
include "rspcimdv.mm"
include "com12.mm"
include "sylbir.mm"
include "expcom.mm"
include "com13.mm"
include "exp31.mm"
include "rexlimivv.mm"
include "mpcom.mm"
include "mp2d.mm"

theorem friendshipgt3
  let vw: setvar w
  let vv: setvar v
  let cG: class G
  let cV: class V
  let vp: setvar p
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  assume frgrreggt1.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G w
  disjoint v w
  disjoint V w
  disjoint G p
  disjoint K p
  disjoint V p
  disjoint K v
  disjoint G a
  disjoint G b
  disjoint a b
  disjoint K a
  disjoint K b
  disjoint V a
  disjoint V b
  disjoint G k
  disjoint V k
  disjoint G m
  disjoint G t
  disjoint G u
  disjoint k m
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint V m
  disjoint V t
  disjoint V u
  assert |- ( ( G e. FriendGraph /\ V e. Fin /\ 3 < ( # ` V ) ) -> E. v e. V A. w e. ( V \ { v } ) { v , w } e. ( Edg ` G ) )

  proof
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    c3
    cV
    chash
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    vu
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    vk
    cv
    #
    wceq
    #
    vu
    cV
    wrex
    #
    cG
    @8
    crusgr
    wbr
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
    @12
    csn
    cdif
    wral
    vv
    cV
    wrex
    #
    wo
    #
    wi
    #
    vk
    cn0
    wral
    #
    @11
    wn
    #
    vk
    cn0
    wral
    #
    @14
    @0
    @1
    @17
    @3
    vw
    vv
    vk
    @13
    cG
    cV
    vu
    frgrreggt1.v
    @13
    eqid
    frgrregorufrg
    3ad2ant1
    vk
    cG
    cV
    frgrreggt1.v
    frgrogt3nreg
    vt
    cv
    #
    @6
    cfv
    #
    vm
    cv
    #
    wceq
    #
    vm
    cn0
    wrex
    vt
    cV
    wrex
    #
    @4
    @17
    @19
    @14
    wi
    wi
    #
    @4
    cG
    cfusgr
    wcel
    #
    cV
    c0
    wne
    #
    @24
    @0
    @1
    @26
    @3
    @0
    @1
    wa
    cG
    cusgr
    wcel
    #
    @1
    wa
    @26
    @0
    @28
    @1
    cG
    frgrusgr
    anim1i
    cG
    cV
    frgrreggt1.v
    isfusgr
    sylibr
    3adant3
    @1
    @3
    @27
    @0
    @1
    @3
    wa
    #
    @2
    cc0
    wne
    @27
    @29
    @2
    @29
    cc0
    c3
    @2
    @29
    0red
    c3
    cr
    wcel
    @29
    3re
    a1i
    @1
    @2
    cr
    wcel
    @3
    @1
    @2
    cV
    hashcl
    nn0red
    adantr
    cc0
    c3
    clt
    wbr
    @29
    3pos
    a1i
    @1
    @3
    simpr
    lttrd
    gt0ne0d
    @29
    @2
    cc0
    cV
    c0
    @1
    @2
    cc0
    wceq
    cV
    c0
    wceq
    wb
    @3
    cV
    cfn
    hasheq0
    adantr
    necon3bid
    mpbid
    3adant1
    vt
    vm
    cG
    cV
    frgrreggt1.v
    fusgrn0degnn0
    syl2anc
    @23
    @4
    @25
    wi
    vt
    vm
    cV
    cn0
    @20
    cV
    wcel
    #
    @22
    cn0
    wcel
    #
    wa
    #
    @23
    @4
    @25
    @19
    @17
    @32
    @23
    wa
    @4
    wa
    #
    @14
    @17
    @19
    @33
    @14
    wi
    #
    @17
    @19
    wa
    @16
    @18
    wa
    #
    vk
    cn0
    wral
    #
    @34
    @16
    @18
    vk
    cn0
    r19.26
    @33
    @36
    @14
    @33
    @35
    @14
    vk
    @22
    cn0
    @30
    @31
    @23
    @4
    simpllr
    @33
    @8
    @22
    wceq
    #
    wa
    @35
    @14
    wi
    #
    @7
    @22
    wceq
    #
    vu
    cV
    wrex
    #
    cG
    @22
    crusgr
    wbr
    #
    @14
    wo
    #
    wi
    #
    @41
    wn
    #
    wa
    #
    @14
    wi
    #
    @33
    @46
    @37
    @33
    @40
    @46
    @30
    @23
    @40
    @31
    @4
    @39
    @23
    vu
    @20
    cV
    @5
    @20
    wceq
    @7
    @21
    @22
    @5
    @20
    @6
    fveq2
    eqeq1d
    rspcev
    ad4ant13
    @40
    @41
    @14
    ornld
    syl
    adantr
    @37
    @38
    @46
    wb
    @33
    @37
    @35
    @45
    @14
    @37
    @16
    @43
    @18
    @44
    @37
    @10
    @40
    @15
    @42
    @37
    @9
    @39
    vu
    cV
    @8
    @22
    @7
    eqeq2
    rexbidv
    @37
    @11
    @41
    @14
    @8
    @22
    cG
    crusgr
    breq2
    #
    orbi1d
    imbi12d
    @37
    @11
    @41
    @47
    notbid
    anbi12d
    imbi1d
    adantl
    mpbird
    rspcimdv
    com12
    sylbir
    expcom
    com13
    exp31
    rexlimivv
    mpcom
    mp2d
end
