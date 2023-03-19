include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wa.mm"
include "cofs.mm"
include "wceq.mm"
include "simpr2l.mm"
include "jca.mm"
include "simpl1.mm"
include "simpl31.mm"
include "simpl21.mm"
include "cgrrflxd.mm"
include "simpl32.mm"
include "simpl33.mm"
include "3jca.mm"
include "simpr3l.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpr3r.mm"
include "wb.mm"
include "cgrcom.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "simpr2r.mm"
include "cgrtr4d.mm"
include "jca32.mm"
include "cgrextend.mm"
include "sylc.mm"
include "ex.mm"
include "simp1.mm"
include "simp31.mm"
include "simp21.mm"
include "simp32.mm"
include "simp33.mm"
include "brofs.mm"
include "syl333anc.mm"
include "sylibrd.mm"
include "wi.mm"
include "a1i.mm"
include "jcad.mm"
include "5segofs.mm"
include "axcgrid.mm"
include "syl13anc.mm"
include "3syld.mm"

theorem segconeq
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cN: class N
  let cX: class X
  let cY: class Y


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( Q e. ( EE ` N ) /\ X e. ( EE ` N ) /\ Y e. ( EE ` N ) ) ) -> ( ( Q =/= A /\ ( A Btwn <. Q , X >. /\ <. A , X >. Cgr <. B , C >. ) /\ ( A Btwn <. Q , Y >. /\ <. A , Y >. Cgr <. B , C >. ) ) -> X = Y ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cQ
    @1
    wcel
    #
    cX
    @1
    wcel
    #
    cY
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cQ
    cA
    wne
    #
    cA
    cQ
    cX
    cop
    #
    cbtwn
    wbr
    #
    cA
    cX
    cop
    #
    cB
    cC
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cA
    cQ
    cY
    cop
    #
    cbtwn
    wbr
    #
    cA
    cY
    cop
    #
    @15
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    cQ
    cA
    cop
    #
    cX
    cY
    cop
    #
    cop
    @24
    cX
    cX
    cop
    #
    cop
    cofs
    wbr
    #
    @11
    wa
    #
    @25
    @26
    ccgr
    wbr
    #
    cX
    cY
    wceq
    #
    @10
    @23
    @27
    @11
    @10
    @23
    @13
    @13
    wa
    #
    @24
    @24
    ccgr
    wbr
    #
    @14
    @14
    ccgr
    wbr
    #
    wa
    #
    @18
    @12
    ccgr
    wbr
    #
    @20
    @14
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    @27
    @10
    @23
    @38
    @10
    @23
    wa
    #
    @31
    @34
    @37
    @39
    @13
    @13
    @13
    @16
    @11
    @22
    @10
    simpr2l
    #
    @40
    jca
    @39
    @32
    @33
    @39
    cQ
    cA
    cN
    @0
    @5
    @9
    @23
    simpl1
    #
    @6
    @7
    @8
    @0
    @5
    @23
    simpl31
    #
    @2
    @3
    @4
    @0
    @9
    @23
    simpl21
    #
    cgrrflxd
    #
    @39
    cA
    cX
    cN
    @41
    @43
    @6
    @7
    @8
    @0
    @5
    @23
    simpl32
    #
    cgrrflxd
    jca
    @39
    @35
    @36
    @39
    @0
    @6
    @2
    @8
    w3a
    #
    @6
    @2
    @7
    w3a
    #
    w3a
    @19
    @13
    wa
    #
    @32
    @36
    wa
    wa
    @35
    @39
    @0
    @46
    @47
    @41
    @39
    @6
    @2
    @8
    @42
    @43
    @6
    @7
    @8
    @0
    @5
    @23
    simpl33
    #
    3jca
    @39
    @6
    @2
    @7
    @42
    @43
    @45
    3jca
    3jca
    @39
    @48
    @32
    @36
    @39
    @19
    @13
    @19
    @21
    @11
    @17
    @10
    simpr3l
    @40
    jca
    @44
    @39
    cB
    cC
    cA
    cY
    cA
    cX
    cN
    @41
    @2
    @3
    @4
    @0
    @9
    @23
    simpl22
    #
    @2
    @3
    @4
    @0
    @9
    @23
    simpl23
    #
    @43
    @49
    @43
    @45
    @39
    @21
    @15
    @20
    ccgr
    wbr
    #
    @19
    @21
    @11
    @17
    @10
    simpr3r
    @39
    @0
    @2
    @8
    @3
    @4
    @21
    @52
    wb
    @41
    @43
    @49
    @50
    @51
    cA
    cY
    cB
    cC
    cN
    cgrcom
    syl122anc
    mpbid
    @39
    @16
    @15
    @14
    ccgr
    wbr
    #
    @13
    @16
    @11
    @22
    @10
    simpr2r
    @39
    @0
    @2
    @7
    @3
    @4
    @16
    @53
    wb
    @41
    @43
    @45
    @50
    @51
    cA
    cX
    cB
    cC
    cN
    cgrcom
    syl122anc
    mpbid
    cgrtr4d
    #
    jca32
    cQ
    cA
    cY
    cQ
    cA
    cX
    cN
    cgrextend
    sylc
    @54
    jca
    3jca
    ex
    @10
    @0
    @6
    @2
    @7
    @8
    @6
    @2
    @7
    @7
    @27
    @38
    wb
    @0
    @5
    @9
    simp1
    #
    @0
    @5
    @6
    @7
    @8
    simp31
    #
    @0
    @2
    @3
    @4
    @9
    simp21
    #
    @0
    @5
    @6
    @7
    @8
    simp32
    #
    @0
    @5
    @6
    @7
    @8
    simp33
    #
    @56
    @57
    @58
    @58
    cQ
    cA
    cX
    cY
    cQ
    cA
    cX
    cX
    cN
    brofs
    syl333anc
    sylibrd
    @23
    @11
    wi
    @10
    @11
    @17
    @22
    simp1
    a1i
    jcad
    @10
    @0
    @6
    @2
    @7
    @8
    @6
    @2
    @7
    @7
    @28
    @29
    wi
    @55
    @56
    @57
    @58
    @59
    @56
    @57
    @58
    @58
    cQ
    cA
    cX
    cY
    cQ
    cA
    cX
    cX
    cN
    5segofs
    syl333anc
    @10
    @0
    @7
    @8
    @7
    @29
    @30
    wi
    @55
    @58
    @59
    @58
    cX
    cY
    cX
    cN
    axcgrid
    syl13anc
    3syld
end
