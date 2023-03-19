include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cz.mm"
include "cicc.mm"
include "cfv.mm"
include "wss.mm"
include "cioo.mm"
include "cin.mm"
include "c0.mm"
include "w3o.mm"
include "cxp.mm"
include "cle.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "dyadf.mm"
include "ffn.mm"
include "ovelrn.mm"
include "anbi12d.mm"
include "mp2b.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "nn0re.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "dyaddisjlem.mm"
include "wbr.mm"
include "ancom.mm"
include "anbi12i.mm"
include "sylanb.mm"
include "wo.mm"
include "orcom.mm"
include "incom.mm"
include "eqeq1i.mm"
include "orbi12i.mm"
include "df-3or.mm"
include "3bitr4i.mm"
include "sylib.mm"
include "lecasei.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simpr.mm"
include "sseq12d.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "3orbi123d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "rexlimivv.mm"
include "sylbi.mm"

theorem dyaddisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint F w
  disjoint F z
  assert |- ( ( A e. ran F /\ B e. ran F ) -> ( ( [,] ` A ) C_ ( [,] ` B ) \/ ( [,] ` B ) C_ ( [,] ` A ) \/ ( ( (,) ` A ) i^i ( (,) ` B ) ) = (/) ) )

  proof
    cA
    cF
    crn
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    va
    cv
    #
    vc
    cv
    #
    cF
    co
    #
    wceq
    #
    vc
    cn0
    wrex
    #
    cB
    vb
    cv
    #
    vd
    cv
    #
    cF
    co
    #
    wceq
    #
    vd
    cn0
    wrex
    #
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    cA
    cicc
    cfv
    #
    cB
    cicc
    cfv
    #
    wss
    #
    @17
    @16
    wss
    #
    cA
    cioo
    cfv
    #
    cB
    cioo
    cfv
    #
    cin
    #
    c0
    wceq
    #
    w3o
    #
    @3
    @8
    va
    cz
    wrex
    #
    @13
    vb
    cz
    wrex
    #
    wa
    #
    @15
    cz
    cn0
    cxp
    #
    cle
    cr
    cr
    cxp
    cin
    #
    cF
    wf
    cF
    @28
    wfn
    #
    @3
    @27
    wb
    vx
    vy
    cF
    dyadmbl.1
    dyadf
    @28
    @29
    cF
    ffn
    @30
    @1
    @25
    @2
    @26
    va
    vc
    cz
    cn0
    cA
    cF
    ovelrn
    vb
    vd
    cz
    cn0
    cB
    cF
    ovelrn
    anbi12d
    mp2b
    @8
    @13
    va
    vb
    cz
    cz
    reeanv
    bitr4i
    @14
    @24
    va
    vb
    cz
    cz
    @14
    @7
    @12
    wa
    #
    vd
    cn0
    wrex
    vc
    cn0
    wrex
    @4
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    wa
    #
    @24
    @7
    @12
    vc
    vd
    cn0
    cn0
    reeanv
    @34
    @31
    @24
    vc
    vd
    cn0
    cn0
    @34
    @5
    cn0
    wcel
    #
    @10
    cn0
    wcel
    #
    wa
    #
    wa
    #
    @24
    @31
    @6
    cicc
    cfv
    #
    @11
    cicc
    cfv
    #
    wss
    #
    @40
    @39
    wss
    #
    @6
    cioo
    cfv
    #
    @11
    cioo
    cfv
    #
    cin
    #
    c0
    wceq
    #
    w3o
    #
    @38
    @47
    @5
    @10
    @35
    @5
    cr
    wcel
    @34
    @36
    @5
    nn0re
    ad2antrl
    @36
    @10
    cr
    wcel
    @34
    @35
    @10
    nn0re
    ad2antll
    vx
    vy
    @4
    @9
    @5
    @10
    cF
    dyadmbl.1
    dyaddisjlem
    @38
    @10
    @5
    cle
    wbr
    #
    wa
    @42
    @41
    @44
    @43
    cin
    #
    c0
    wceq
    #
    w3o
    #
    @47
    @38
    @33
    @32
    wa
    #
    @36
    @35
    wa
    #
    wa
    @48
    @51
    @34
    @52
    @37
    @53
    @32
    @33
    ancom
    @35
    @36
    ancom
    anbi12i
    vx
    vy
    @9
    @4
    @10
    @5
    cF
    dyadmbl.1
    dyaddisjlem
    sylanb
    @42
    @41
    wo
    #
    @50
    wo
    @41
    @42
    wo
    #
    @46
    wo
    @51
    @47
    @54
    @55
    @50
    @46
    @42
    @41
    orcom
    @49
    @45
    c0
    @44
    @43
    incom
    eqeq1i
    orbi12i
    @42
    @41
    @50
    df-3or
    @41
    @42
    @46
    df-3or
    3bitr4i
    sylib
    lecasei
    @31
    @18
    @41
    @19
    @42
    @23
    @46
    @31
    @16
    @39
    @17
    @40
    @31
    cA
    @6
    cicc
    @7
    @12
    simpl
    #
    fveq2d
    #
    @31
    cB
    @11
    cicc
    @7
    @12
    simpr
    #
    fveq2d
    #
    sseq12d
    @31
    @17
    @40
    @16
    @39
    @59
    @57
    sseq12d
    @31
    @22
    @45
    c0
    @31
    @20
    @43
    @21
    @44
    @31
    cA
    @6
    cioo
    @56
    fveq2d
    @31
    cB
    @11
    cioo
    @58
    fveq2d
    ineq12d
    eqeq1d
    3orbi123d
    syl5ibrcom
    rexlimdvva
    syl5bir
    rexlimivv
    sylbi
end
