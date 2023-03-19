include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "ccgr.mm"
include "wreu.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "cbtwn.mm"
include "wo.mm"
include "segcon2.mm"
include "adantr.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpr.mm"
include "simpl2r.mm"
include "broutsideof2.mm"
include "syl13anc.mm"
include "simp3.mm"
include "simpllr.mm"
include "adantl.mm"
include "wceq.mm"
include "simprlr.mm"
include "simp2l.mm"
include "anim1i.mm"
include "simpl3.mm"
include "cgrdegen.mm"
include "syl3anc.mm"
include "mpd.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "necomd.mm"
include "simplll.mm"
include "simprr.mm"
include "3jca.mm"
include "expr.mm"
include "impbid2.mm"
include "bitrd.mm"
include "orcom.mm"
include "syl6bb.mm"
include "pm5.32rd.mm"
include "an32s.mm"
include "rexbidva.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simprl.mm"
include "outsideofeq.mm"
include "imp.mm"
include "syl2an.mm"
include "an4s.mm"
include "exp32.mm"
include "ralrimivv.mm"
include "opeq1.mm"
include "breq2d.mm"
include "opeq2.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "reu4.mm"
include "sylanbrc.mm"
include "ex.mm"

theorem outsideofeu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cN: class N
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint N x
  disjoint R x
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint N y
  disjoint R y
  disjoint x y
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ R e. ( EE ` N ) ) /\ ( B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( ( R =/= A /\ B =/= C ) -> E! x e. ( EE ` N ) ( A OutsideOf <. x , R >. /\ <. A , x >. Cgr <. B , C >. ) ) )

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
    cR
    @1
    wcel
    #
    wa
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cR
    cA
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    cA
    vx
    cv
    #
    cR
    cop
    #
    coutsideof
    wbr
    #
    cA
    @12
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
    vx
    @1
    wreu
    #
    @8
    @11
    wa
    #
    @18
    vx
    @1
    wrex
    #
    @18
    cA
    vy
    cv
    #
    cR
    cop
    #
    coutsideof
    wbr
    #
    cA
    @22
    cop
    #
    @16
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    @19
    @20
    @21
    cR
    @15
    cbtwn
    wbr
    #
    @12
    cA
    cR
    cop
    cbtwn
    wbr
    #
    wo
    #
    @17
    wa
    #
    vx
    @1
    wrex
    #
    @8
    @35
    @11
    vx
    cR
    cB
    cC
    cA
    cN
    segcon2
    adantr
    @20
    @18
    @34
    vx
    @1
    @8
    @12
    @1
    wcel
    #
    @11
    @18
    @34
    wb
    @8
    @36
    wa
    #
    @11
    wa
    @17
    @14
    @33
    @37
    @11
    @17
    @14
    @33
    wb
    @37
    @11
    @17
    wa
    #
    wa
    #
    @14
    @32
    @31
    wo
    #
    @33
    @39
    @14
    @12
    cA
    wne
    #
    @9
    @40
    w3a
    #
    @40
    @37
    @14
    @42
    wb
    #
    @38
    @37
    @0
    @2
    @36
    @3
    @43
    @0
    @4
    @7
    @36
    simpl1
    #
    @2
    @3
    @0
    @7
    @36
    simpl2l
    @8
    @36
    simpr
    @2
    @3
    @0
    @7
    @36
    simpl2r
    @12
    cR
    cA
    cN
    broutsideof2
    syl13anc
    adantr
    @39
    @42
    @40
    @41
    @9
    @40
    simp3
    @37
    @38
    @40
    @42
    @37
    @38
    @40
    wa
    #
    wa
    #
    @41
    @9
    @40
    @46
    cA
    @12
    @46
    cA
    @12
    wne
    @10
    @45
    @10
    @37
    @9
    @10
    @17
    @40
    simpllr
    adantl
    @46
    cA
    @12
    cB
    cC
    @46
    @17
    cA
    @12
    wceq
    cB
    cC
    wceq
    wb
    #
    @37
    @11
    @17
    @40
    simprlr
    @37
    @17
    @47
    wi
    #
    @45
    @37
    @0
    @2
    @36
    wa
    @7
    @48
    @44
    @8
    @2
    @36
    @0
    @2
    @3
    @7
    simp2l
    anim1i
    @0
    @4
    @7
    @36
    simpl3
    cA
    @12
    cB
    cC
    cN
    cgrdegen
    syl3anc
    adantr
    mpd
    necon3bid
    mpbird
    necomd
    @45
    @9
    @37
    @9
    @10
    @17
    @40
    simplll
    adantl
    @37
    @38
    @40
    simprr
    3jca
    expr
    impbid2
    bitrd
    @32
    @31
    orcom
    syl6bb
    expr
    pm5.32rd
    an32s
    rexbidva
    mpbird
    @20
    @30
    vx
    vy
    @1
    @1
    @20
    @36
    @22
    @1
    wcel
    #
    wa
    #
    @28
    @29
    @8
    @50
    @11
    @28
    @29
    @8
    @50
    wa
    #
    @0
    @2
    @3
    @5
    w3a
    #
    @6
    @36
    @49
    w3a
    #
    w3a
    #
    @28
    @29
    @11
    @28
    wa
    @51
    @0
    @52
    @53
    @0
    @4
    @7
    @50
    simpl1
    @51
    @2
    @3
    @5
    @2
    @3
    @0
    @7
    @50
    simpl2l
    @2
    @3
    @0
    @7
    @50
    simpl2r
    @5
    @6
    @0
    @4
    @50
    simpl3l
    3jca
    @51
    @6
    @36
    @49
    @5
    @6
    @0
    @4
    @50
    simpl3r
    @8
    @36
    @49
    simprl
    @8
    @36
    @49
    simprr
    3jca
    3jca
    @11
    @28
    simpr
    @54
    @28
    @29
    cA
    cB
    cC
    cR
    cN
    @12
    @22
    outsideofeq
    imp
    syl2an
    an4s
    exp32
    ralrimivv
    @18
    @27
    vx
    vy
    @1
    @29
    @14
    @24
    @17
    @26
    @29
    @13
    @23
    cA
    coutsideof
    @12
    @22
    cR
    opeq1
    breq2d
    @29
    @15
    @25
    @16
    ccgr
    @12
    @22
    cA
    opeq2
    breq1d
    anbi12d
    reu4
    sylanbrc
    ex
end
