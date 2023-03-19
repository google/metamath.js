include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "wo.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wb.mm"
include "elpadd.mm"
include "adantr.mm"
include "wi.mm"
include "simpl2.mm"
include "sseld.mm"
include "cbs.mm"
include "cfv.mm"
include "simpll1.mm"
include "ssel2.mm"
include "3ad2antl2.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpl3.mm"
include "sselda.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "reximdva0.mm"
include "exp31.mm"
include "com23.mm"
include "imp.mm"
include "ancld.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rexbidv.mm"
include "rspcev.mm"
include "syl6.mm"
include "adantrl.mm"
include "jcad.mm"
include "wex.mm"
include "latlej2.mm"
include "ex.mm"
include "oveq2.mm"
include "impancom.mm"
include "eximdv.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "adantrr.mm"
include "jaod.mm"
include "pm4.72.mm"
include "sylib.mm"
include "bitr4d.mm"

theorem elpaddn0
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vq: setvar q
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint q r
  disjoint K q
  disjoint K r
  disjoint X q
  disjoint Y q
  disjoint Y r
  disjoint S q
  disjoint S r
  disjoint A q
  disjoint A r
  disjoint .\/ q
  disjoint .\/ r
  disjoint .<_ q
  disjoint .<_ r
  disjoint X r
  disjoint h m
  disjoint h n
  disjoint h p
  disjoint h s
  disjoint A h
  disjoint m n
  disjoint m p
  disjoint m s
  disjoint A m
  disjoint n p
  disjoint n s
  disjoint A n
  disjoint p s
  disjoint A p
  disjoint A s
  disjoint .\/ h
  disjoint h q
  disjoint h r
  disjoint K h
  disjoint m q
  disjoint m r
  disjoint K m
  disjoint n q
  disjoint n r
  disjoint K n
  disjoint p q
  disjoint p r
  disjoint K p
  disjoint q s
  disjoint r s
  disjoint K s
  disjoint .<_ h
  disjoint .\/ m
  disjoint .\/ n
  disjoint .\/ s
  disjoint .<_ m
  disjoint .<_ n
  disjoint .<_ s
  disjoint X m
  disjoint X n
  disjoint X p
  disjoint X s
  disjoint Y m
  disjoint Y n
  disjoint Y p
  disjoint Y s
  disjoint .\/ p
  disjoint .<_ p
  disjoint S p
  disjoint .+ s
  assert |- ( ( ( K e. Lat /\ X C_ A /\ Y C_ A ) /\ ( X =/= (/) /\ Y =/= (/) ) ) -> ( S e. ( X .+ Y ) <-> ( S e. A /\ E. q e. X E. r e. Y S .<_ ( q .\/ r ) ) ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cX
    c0
    wne
    #
    cY
    c0
    wne
    #
    wa
    #
    wa
    #
    cS
    cX
    cY
    c.pl
    co
    wcel
    #
    cS
    cX
    wcel
    #
    cS
    cY
    wcel
    #
    wo
    #
    cS
    cA
    wcel
    #
    cS
    vq
    cv
    #
    vr
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    cY
    wrex
    #
    vq
    cX
    wrex
    #
    wa
    #
    wo
    #
    @19
    @3
    @8
    @20
    wb
    @6
    cA
    clat
    c.pl
    cS
    c.or
    cK
    c.le
    cX
    cY
    vr
    vq
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpadd
    adantr
    @7
    @11
    @19
    wi
    @19
    @20
    wb
    @7
    @9
    @19
    @10
    @7
    @9
    @12
    @18
    @7
    cX
    cA
    cS
    @0
    @1
    @2
    @6
    simpl2
    sseld
    @3
    @5
    @9
    @18
    wi
    @4
    @3
    @5
    wa
    #
    @9
    @9
    cS
    cS
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    cY
    wrex
    #
    wa
    @18
    @21
    @9
    @24
    @3
    @5
    @9
    @24
    wi
    @3
    @9
    @5
    @24
    @3
    @9
    @5
    @24
    @3
    @9
    wa
    #
    @23
    vr
    cY
    @25
    @14
    cY
    wcel
    #
    wa
    #
    @0
    cS
    cK
    cbs
    cfv
    #
    wcel
    #
    @14
    @28
    wcel
    #
    @23
    @0
    @1
    @2
    @9
    @26
    simpll1
    @27
    @12
    @29
    @25
    @12
    @26
    @1
    @0
    @9
    @12
    @2
    cX
    cA
    cS
    ssel2
    3ad2antl2
    adantr
    cA
    @28
    cS
    cK
    @28
    eqid
    #
    paddfval.a
    atbase
    #
    syl
    @27
    @14
    cA
    wcel
    @30
    @25
    cY
    cA
    @14
    @0
    @1
    @2
    @9
    simpl3
    sselda
    cA
    @28
    @14
    cK
    @31
    paddfval.a
    atbase
    syl
    @28
    c.or
    cK
    c.le
    cS
    @14
    @31
    paddfval.l
    paddfval.j
    latlej1
    syl3anc
    reximdva0
    exp31
    com23
    imp
    ancld
    @17
    @24
    vq
    cS
    cX
    @13
    cS
    wceq
    #
    @16
    @23
    vr
    cY
    @33
    @15
    @22
    cS
    c.le
    @13
    cS
    @14
    c.or
    oveq1
    breq2d
    rexbidv
    rspcev
    syl6
    adantrl
    jcad
    @7
    @10
    @12
    @18
    @7
    cY
    cA
    cS
    @0
    @1
    @2
    @6
    simpl3
    sseld
    @3
    @4
    @10
    @18
    wi
    @5
    @3
    @10
    @4
    @18
    @3
    @10
    wa
    #
    @13
    cX
    wcel
    #
    vq
    wex
    @35
    @17
    wa
    #
    vq
    wex
    @4
    @18
    @34
    @35
    @36
    vq
    @34
    @35
    @17
    @3
    @35
    @10
    @17
    @3
    @35
    wa
    #
    @10
    @10
    cS
    @13
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    @17
    @37
    @10
    @39
    @37
    @10
    @39
    @37
    @10
    wa
    #
    @0
    @13
    @28
    wcel
    #
    @29
    @39
    @0
    @1
    @2
    @35
    @10
    simpll1
    @40
    @13
    cA
    wcel
    #
    @41
    @37
    @42
    @10
    @1
    @0
    @35
    @42
    @2
    cX
    cA
    @13
    ssel2
    3ad2antl2
    adantr
    cA
    @28
    @13
    cK
    @31
    paddfval.a
    atbase
    syl
    @40
    @12
    @29
    @37
    cY
    cA
    cS
    @0
    @1
    @2
    @35
    simpl3
    sselda
    @32
    syl
    @28
    c.or
    cK
    c.le
    @13
    cS
    @31
    paddfval.l
    paddfval.j
    latlej2
    syl3anc
    ex
    ancld
    @16
    @39
    vr
    cS
    cY
    @14
    cS
    wceq
    @15
    @38
    cS
    c.le
    @14
    cS
    @13
    c.or
    oveq2
    breq2d
    rspcev
    syl6
    impancom
    ancld
    eximdv
    vq
    cX
    n0
    @17
    vq
    cX
    df-rex
    3imtr4g
    impancom
    adantrr
    jcad
    jaod
    @11
    @19
    pm4.72
    sylib
    bitr4d
end
