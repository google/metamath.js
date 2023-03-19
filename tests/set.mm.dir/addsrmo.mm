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
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wer.mm"
include "enrer.mm"
include "a1i.mm"
include "wbr.mm"
include "prsrlem1.mm"
include "addcmpblnr.mm"
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

theorem addsrmo
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
  assert |- ( ( A e. ( ( P. X. P. ) /. ~R ) /\ B e. ( ( P. X. P. ) /. ~R ) ) -> E* z E. w E. v E. u E. t ( ( A = [ <. w , v >. ] ~R /\ B = [ <. u , t >. ] ~R ) /\ z = [ <. ( w +P. u ) , ( v +P. t ) >. ] ~R ) )

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
    cpp
    co
    #
    @4
    @9
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
    @18
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
    @23
    wceq
    #
    wi
    #
    vq
    wal
    vz
    wal
    #
    @22
    vz
    wmo
    @2
    @22
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
    @23
    @31
    @36
    cpp
    co
    #
    @32
    @37
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
    @28
    wi
    #
    vq
    wal
    vz
    wal
    @30
    @2
    @51
    vz
    vq
    @2
    @22
    @49
    @28
    @2
    @21
    @49
    @28
    wi
    #
    vw
    vv
    @2
    @20
    @52
    vu
    vt
    @2
    @20
    @52
    @2
    @20
    wa
    #
    @48
    @28
    vs
    vf
    @53
    @47
    @28
    vg
    vh
    @2
    @20
    @47
    @28
    @2
    @20
    @47
    wa
    wa
    @18
    @45
    @14
    @23
    @2
    @20
    @41
    @18
    @45
    wceq
    #
    @46
    @2
    @13
    @41
    @54
    @19
    @2
    @13
    @41
    wa
    wa
    #
    @17
    @44
    cer
    @0
    @0
    cer
    wer
    @55
    enrer
    a1i
    @55
    @3
    cnp
    wcel
    @4
    cnp
    wcel
    wa
    @31
    cnp
    wcel
    @32
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
    @36
    cnp
    wcel
    @37
    cnp
    wcel
    wa
    wa
    wa
    #
    @3
    @32
    cpp
    co
    @4
    @31
    cpp
    co
    wceq
    @8
    @37
    cpp
    co
    @9
    @36
    cpp
    co
    wceq
    wa
    #
    wa
    @17
    @44
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
    @56
    @57
    @58
    @3
    @4
    @31
    @32
    @36
    @37
    @8
    @9
    addcmpblnr
    imp
    syl
    erthi
    adantrlr
    adantrrr
    @2
    @13
    @19
    @47
    simprlr
    @2
    @20
    @41
    @46
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
    @29
    @51
    vz
    vq
    @27
    @50
    @28
    @26
    @49
    @22
    @25
    @35
    @12
    wa
    #
    @23
    @31
    @8
    cpp
    co
    #
    @32
    @9
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
    @47
    vw
    vv
    vu
    vt
    vs
    vf
    vg
    vh
    @3
    @31
    wceq
    #
    @4
    @32
    wceq
    #
    wa
    #
    @13
    @59
    @24
    @64
    @67
    @7
    @35
    @12
    @67
    @6
    @34
    cA
    @67
    @5
    @33
    cer
    @3
    @4
    @31
    @32
    opeq12
    eceq1d
    eqeq2d
    anbi1d
    @67
    @18
    @63
    @23
    @67
    @17
    @62
    cer
    @67
    @15
    @60
    @16
    @61
    @67
    @3
    @31
    @8
    cpp
    @65
    @66
    simpl
    oveq1d
    @67
    @4
    @32
    @9
    cpp
    @65
    @66
    simpr
    oveq1d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    @8
    @36
    wceq
    #
    @9
    @37
    wceq
    #
    wa
    #
    @59
    @41
    @64
    @46
    @70
    @12
    @40
    @35
    @70
    @11
    @39
    cB
    @70
    @10
    @38
    cer
    @8
    @9
    @36
    @37
    opeq12
    eceq1d
    eqeq2d
    anbi2d
    @70
    @63
    @45
    @23
    @70
    @62
    @44
    cer
    @70
    @60
    @42
    @61
    @43
    @70
    @8
    @36
    @31
    cpp
    @68
    @69
    simpl
    oveq2d
    @70
    @9
    @37
    @32
    cpp
    @68
    @69
    simpr
    oveq2d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    cbvex4v
    anbi2i
    imbi1i
    2albii
    sylibr
    @22
    @26
    vz
    vq
    @28
    @20
    @25
    vw
    vv
    vu
    vt
    @28
    @19
    @24
    @13
    @14
    @23
    @18
    eqeq1
    anbi2d
    4exbidv
    mo4
    sylibr
end
