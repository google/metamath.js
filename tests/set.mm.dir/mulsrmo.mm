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
include "cmp.mm"
include "co.mm"
include "cpp.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wer.mm"
include "enrer.mm"
include "a1i.mm"
include "wbr.mm"
include "prsrlem1.mm"
include "mulcmpblnr.mm"
include "imp.mm"
include "syl.mm"
include "erthi.mm"
include "adantrlr.mm"
include "adantrrr.mm"
include "simprlr.mm"
include "simprrr.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "exlimdvv.mm"
include "ex.mm"
include "impd.mm"
include "alrimivv.mm"
include "opeq12.mm"
include "eceq1d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "oveq2d.mm"
include "cbvex4v.mm"
include "anbi2i.mm"
include "imbi1i.mm"
include "2albii.mm"
include "sylibr.mm"
include "eqeq1.mm"
include "4exbidv.mm"
include "mo4.mm"

theorem mulsrmo
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vq: setvar q
  let vs: setvar s

  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t z
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A q
  disjoint A s
  disjoint f g
  disjoint f h
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint g h
  disjoint g q
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g z
  disjoint h q
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h z
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B q
  disjoint B s
  assert |- ( ( A e. ( ( P. X. P. ) /. ~R ) /\ B e. ( ( P. X. P. ) /. ~R ) ) -> E* z E. w E. v E. u E. t ( ( A = [ <. w , v >. ] ~R /\ B = [ <. u , t >. ] ~R ) /\ z = [ <. ( ( w .P. u ) +P. ( v .P. t ) ) , ( ( w .P. t ) +P. ( v .P. u ) ) >. ] ~R ) )

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
    cB
    @1
    wcel
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
    vz
    cv
    #
    @3
    @8
    cmp
    co
    #
    @4
    @9
    cmp
    co
    #
    cpp
    co
    #
    @3
    @9
    cmp
    co
    #
    @4
    @8
    cmp
    co
    #
    cpp
    co
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
    vt
    wex
    vu
    wex
    #
    vv
    wex
    vw
    wex
    #
    @13
    vq
    cv
    #
    @22
    wceq
    #
    wa
    #
    vt
    wex
    vu
    wex
    vv
    wex
    vw
    wex
    #
    wa
    #
    @14
    @27
    wceq
    #
    wi
    #
    vq
    wal
    vz
    wal
    #
    @26
    vz
    wmo
    @2
    @26
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
    @27
    @35
    @40
    cmp
    co
    #
    @36
    @41
    cmp
    co
    #
    cpp
    co
    #
    @35
    @41
    cmp
    co
    #
    @36
    @40
    cmp
    co
    #
    cpp
    co
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
    vh
    wex
    vg
    wex
    #
    vf
    wex
    vs
    wex
    #
    wa
    #
    @32
    wi
    #
    vq
    wal
    vz
    wal
    @34
    @2
    @59
    vz
    vq
    @2
    @26
    @57
    @32
    @2
    @25
    @57
    @32
    wi
    #
    vw
    vv
    @2
    @24
    @60
    vu
    vt
    @2
    @24
    @60
    @2
    @24
    wa
    #
    @56
    @32
    vs
    vf
    @61
    @55
    @32
    vg
    vh
    @2
    @24
    @55
    @32
    @2
    @24
    @55
    wa
    wa
    @22
    @53
    @14
    @27
    @2
    @24
    @45
    @22
    @53
    wceq
    #
    @54
    @2
    @13
    @45
    @62
    @23
    @2
    @13
    @45
    wa
    wa
    #
    @21
    @52
    cer
    @0
    @0
    cer
    wer
    @63
    enrer
    a1i
    @63
    @3
    cnp
    wcel
    @4
    cnp
    wcel
    wa
    @35
    cnp
    wcel
    @36
    cnp
    wcel
    wa
    wa
    @8
    cnp
    wcel
    @9
    cnp
    wcel
    wa
    @40
    cnp
    wcel
    @41
    cnp
    wcel
    wa
    wa
    wa
    #
    @3
    @36
    cpp
    co
    @4
    @35
    cpp
    co
    wceq
    @8
    @41
    cpp
    co
    @9
    @40
    cpp
    co
    wceq
    wa
    #
    wa
    @21
    @52
    cer
    wbr
    #
    vw
    vv
    vu
    vt
    cA
    cB
    vf
    vg
    vh
    vs
    prsrlem1
    @64
    @65
    @66
    @3
    @4
    @35
    @36
    @40
    @41
    @8
    @9
    mulcmpblnr
    imp
    syl
    erthi
    adantrlr
    adantrrr
    @2
    @13
    @23
    @55
    simprlr
    @2
    @24
    @45
    @54
    simprrr
    3eqtr4d
    expr
    exlimdvv
    exlimdvv
    ex
    exlimdvv
    exlimdvv
    impd
    alrimivv
    @33
    @59
    vz
    vq
    @31
    @58
    @32
    @30
    @57
    @26
    @29
    @39
    @12
    wa
    #
    @27
    @35
    @8
    cmp
    co
    #
    @36
    @9
    cmp
    co
    #
    cpp
    co
    #
    @35
    @9
    cmp
    co
    #
    @36
    @8
    cmp
    co
    #
    cpp
    co
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    wa
    @55
    vw
    vv
    vu
    vt
    vs
    vf
    vg
    vh
    @3
    @35
    wceq
    #
    @4
    @36
    wceq
    #
    wa
    #
    @13
    @67
    @28
    @76
    @79
    @7
    @39
    @12
    @79
    @6
    @38
    cA
    @79
    @5
    @37
    cer
    @3
    @4
    @35
    @36
    opeq12
    eceq1d
    eqeq2d
    anbi1d
    @79
    @22
    @75
    @27
    @79
    @21
    @74
    cer
    @79
    @17
    @70
    @20
    @73
    @79
    @15
    @68
    @16
    @69
    cpp
    @79
    @3
    @35
    @8
    cmp
    @77
    @78
    simpl
    #
    oveq1d
    @79
    @4
    @36
    @9
    cmp
    @77
    @78
    simpr
    #
    oveq1d
    oveq12d
    @79
    @18
    @71
    @19
    @72
    cpp
    @79
    @3
    @35
    @9
    cmp
    @80
    oveq1d
    @79
    @4
    @36
    @8
    cmp
    @81
    oveq1d
    oveq12d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    @8
    @40
    wceq
    #
    @9
    @41
    wceq
    #
    wa
    #
    @67
    @45
    @76
    @54
    @84
    @12
    @44
    @39
    @84
    @11
    @43
    cB
    @84
    @10
    @42
    cer
    @8
    @9
    @40
    @41
    opeq12
    eceq1d
    eqeq2d
    anbi2d
    @84
    @75
    @53
    @27
    @84
    @74
    @52
    cer
    @84
    @70
    @48
    @73
    @51
    @84
    @68
    @46
    @69
    @47
    cpp
    @84
    @8
    @40
    @35
    cmp
    @82
    @83
    simpl
    #
    oveq2d
    @84
    @9
    @41
    @36
    cmp
    @82
    @83
    simpr
    #
    oveq2d
    oveq12d
    @84
    @71
    @49
    @72
    @50
    cpp
    @84
    @9
    @41
    @35
    cmp
    @86
    oveq2d
    @84
    @8
    @40
    @36
    cmp
    @85
    oveq2d
    oveq12d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    cbvex4v
    anbi2i
    imbi1i
    2albii
    sylibr
    @26
    @30
    vz
    vq
    @32
    @24
    @29
    vw
    vv
    vu
    vt
    @32
    @23
    @28
    @13
    @14
    @27
    @22
    eqeq1
    anbi2d
    4exbidv
    mo4
    sylibr
end
