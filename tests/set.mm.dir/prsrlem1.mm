include "cnp.mm"
include "cxp.mm"
include "cer.mm"
include "cqs.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "cec.mm"
include "wceq.mm"
include "cpp.mm"
include "co.mm"
include "cdm.mm"
include "wer.mm"
include "enrer.mm"
include "erdm.mm"
include "ax-mp.mm"
include "simprll.mm"
include "simpll.mm"
include "eqeltrrd.mm"
include "ecelqsdm.mm"
include "sylancr.mm"
include "opelxp.mm"
include "sylib.mm"
include "simprrl.mm"
include "jca.mm"
include "simprlr.mm"
include "simplr.mm"
include "simprrr.mm"
include "wbr.mm"
include "eqtr3d.mm"
include "a1i.mm"
include "erth.mm"
include "mpbird.mm"
include "wb.mm"
include "df-enr.mm"
include "ecopoveq.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "jca31.mm"

theorem prsrlem1
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y

  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint x y
  assert |- ( ( ( A e. ( ( P. X. P. ) /. ~R ) /\ B e. ( ( P. X. P. ) /. ~R ) ) /\ ( ( A = [ <. w , v >. ] ~R /\ B = [ <. u , t >. ] ~R ) /\ ( A = [ <. s , f >. ] ~R /\ B = [ <. g , h >. ] ~R ) ) ) -> ( ( ( ( w e. P. /\ v e. P. ) /\ ( s e. P. /\ f e. P. ) ) /\ ( ( u e. P. /\ t e. P. ) /\ ( g e. P. /\ h e. P. ) ) ) /\ ( ( w +P. f ) = ( v +P. s ) /\ ( u +P. h ) = ( t +P. g ) ) ) )

  proof
    cA
    cnp
    cnp
    cxp
    #
    cer
    cqs
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cA
    vw
    cv
    #
    vv
    cv
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    cB
    vu
    cv
    #
    vt
    cv
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    wa
    #
    cA
    vs
    cv
    #
    vf
    cv
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    cB
    vg
    cv
    #
    vh
    cv
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @5
    cnp
    wcel
    @6
    cnp
    wcel
    wa
    #
    @16
    cnp
    wcel
    @17
    cnp
    wcel
    wa
    #
    wa
    @10
    cnp
    wcel
    @11
    cnp
    wcel
    wa
    #
    @21
    cnp
    wcel
    @22
    cnp
    wcel
    wa
    #
    wa
    @5
    @17
    cpp
    co
    @6
    @16
    cpp
    co
    wceq
    #
    @10
    @22
    cpp
    co
    @11
    @21
    cpp
    co
    wceq
    #
    wa
    @28
    @29
    @30
    @28
    @7
    @0
    wcel
    #
    @29
    @28
    cer
    cdm
    @0
    wceq
    #
    @8
    @1
    wcel
    @35
    @0
    cer
    wer
    #
    @36
    enrer
    @0
    cer
    erdm
    ax-mp
    #
    @28
    cA
    @8
    @1
    @4
    @9
    @14
    @26
    simprll
    #
    @2
    @3
    @27
    simpll
    #
    eqeltrrd
    @0
    @7
    cer
    ecelqsdm
    sylancr
    #
    @5
    @6
    cnp
    cnp
    opelxp
    sylib
    #
    @28
    @18
    @0
    wcel
    #
    @30
    @28
    @36
    @19
    @1
    wcel
    @43
    @38
    @28
    cA
    @19
    @1
    @4
    @15
    @20
    @25
    simprrl
    #
    @40
    eqeltrrd
    @0
    @18
    cer
    ecelqsdm
    sylancr
    @16
    @17
    cnp
    cnp
    opelxp
    sylib
    #
    jca
    @28
    @31
    @32
    @28
    @12
    @0
    wcel
    #
    @31
    @28
    @36
    @13
    @1
    wcel
    @46
    @38
    @28
    cB
    @13
    @1
    @4
    @9
    @14
    @26
    simprlr
    #
    @2
    @3
    @27
    simplr
    #
    eqeltrrd
    @0
    @12
    cer
    ecelqsdm
    sylancr
    #
    @10
    @11
    cnp
    cnp
    opelxp
    sylib
    #
    @28
    @23
    @0
    wcel
    #
    @32
    @28
    @36
    @24
    @1
    wcel
    @51
    @38
    @28
    cB
    @24
    @1
    @4
    @15
    @20
    @25
    simprrr
    #
    @48
    eqeltrrd
    @0
    @23
    cer
    ecelqsdm
    sylancr
    @21
    @22
    cnp
    cnp
    opelxp
    sylib
    #
    jca
    @28
    @33
    @34
    @28
    @7
    @18
    cer
    wbr
    #
    @33
    @28
    @54
    @8
    @19
    wceq
    @28
    cA
    @8
    @19
    @39
    @44
    eqtr3d
    @28
    @7
    @18
    cer
    @0
    @37
    @28
    enrer
    a1i
    #
    @41
    erth
    mpbird
    @28
    @29
    @30
    @54
    @33
    wb
    @42
    @45
    vx
    vy
    va
    vb
    vc
    vd
    @5
    @6
    @16
    @17
    cpp
    cer
    cnp
    vx
    vy
    va
    vb
    vc
    vd
    df-enr
    #
    ecopoveq
    syl2anc
    mpbid
    @28
    @12
    @23
    cer
    wbr
    #
    @34
    @28
    @57
    @13
    @24
    wceq
    @28
    cB
    @13
    @24
    @47
    @52
    eqtr3d
    @28
    @12
    @23
    cer
    @0
    @55
    @49
    erth
    mpbird
    @28
    @31
    @32
    @57
    @34
    wb
    @50
    @53
    vx
    vy
    va
    vb
    vc
    vd
    @10
    @11
    @21
    @22
    cpp
    cer
    cnp
    @56
    ecopoveq
    syl2anc
    mpbid
    jca
    jca31
end
