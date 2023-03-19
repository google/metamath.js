include "com.mm"
include "cvv.mm"
include "cv.mm"
include "wf1.mm"
include "cfn.mm"
include "wcel.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "cfv.mm"
include "crn.mm"
include "cint.mm"
include "cdif.mm"
include "cmpt.mm"
include "wo.mm"
include "cif.mm"
include "eqif.mm"
include "mpbi.mm"
include "wf1o.mm"
include "wss.mm"
include "difss.mm"
include "ominf.mm"
include "cun.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "undif.mm"
include "unfi.mm"
include "syl5eqelr.mm"
include "ex.mm"
include "mtoi.mm"
include "fin23lem22.mm"
include "sylancr.mm"
include "adantl.mm"
include "f1of1.mm"
include "f1ss.mm"
include "mpan2.mm"
include "3syl.mm"
include "f1co.mm"
include "syldan.mm"
include "f1eq1.mm"
include "syl5ibrcom.mm"
include "impr.mm"
include "wf.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "fvex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "a1i.mm"
include "fveq2.mm"
include "difeq1d.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "uneq2.mm"
include "sseq2d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "sylib.mm"
include "syl5ib.mm"
include "wb.mm"
include "sseli.mm"
include "anim12i.mm"
include "f1fveq.mm"
include "sylan2.mm"
include "sylibd.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "syl.mm"
include "mpan.mm"
include "syl2an.mm"
include "jaodan.mm"

theorem fin23lem28
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let cG: class G
  assume fin23lem.a: |- U = seqom ( ( i e. _om , u e. _V |-> if ( ( ( t ` i ) i^i u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t )
  assume fin23lem17.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }
  assume fin23lem.b: |- P = { v e. _om | |^| ran U C_ ( t ` v ) }
  assume fin23lem.c: |- Q = ( w e. _om |-> ( iota_ x e. P ( x i^i P ) ~~ w ) )
  assume fin23lem.d: |- R = ( w e. _om |-> ( iota_ x e. ( _om \ P ) ( x i^i ( _om \ P ) ) ~~ w ) )
  assume fin23lem.e: |- Z = if ( P e. Fin , ( t o. R ) , ( ( z e. P |-> ( ( t ` z ) \ |^| ran U ) ) o. Q ) )

  disjoint g i
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g z
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i z
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint a i
  disjoint a u
  disjoint a t
  disjoint F a
  disjoint F t
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint P a
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint a v
  disjoint R a
  disjoint R i
  disjoint R u
  disjoint R v
  disjoint U a
  disjoint U i
  disjoint U u
  disjoint U v
  disjoint U z
  disjoint Z a
  disjoint a g
  disjoint c g
  disjoint c i
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint a b
  disjoint A a
  disjoint b i
  disjoint b u
  disjoint A b
  disjoint A i
  disjoint A u
  disjoint B a
  disjoint B b
  disjoint V a
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint P b
  disjoint b v
  disjoint R b
  disjoint a c
  disjoint b c
  disjoint U b
  disjoint U c
  disjoint a f
  disjoint b f
  disjoint Z b
  disjoint Z f
  disjoint G a
  disjoint b g
  disjoint b t
  disjoint G b
  disjoint f g
  disjoint f t
  disjoint f x
  disjoint G f
  disjoint G g
  disjoint G t
  disjoint G x
  assert |- ( t : _om -1-1-> _V -> Z : _om -1-1-> _V )

  proof
    com
    cvv
    vt
    cv
    #
    wf1
    #
    cP
    cfn
    wcel
    #
    cZ
    @0
    cR
    ccom
    #
    wceq
    #
    wa
    #
    @2
    wn
    #
    cZ
    vz
    cP
    vz
    cv
    #
    @0
    cfv
    #
    cU
    crn
    cint
    #
    cdif
    #
    cmpt
    #
    cQ
    ccom
    #
    wceq
    #
    wa
    #
    wo
    #
    com
    cvv
    cZ
    wf1
    #
    cZ
    @2
    @3
    @12
    cif
    wceq
    @15
    fin23lem.e
    @2
    cZ
    @3
    @12
    eqif
    mpbi
    @1
    @5
    @16
    @14
    @1
    @2
    @4
    @16
    @1
    @2
    wa
    #
    @16
    @4
    com
    cvv
    @3
    wf1
    #
    @1
    @2
    com
    com
    cR
    wf1
    #
    @18
    @17
    com
    com
    cP
    cdif
    #
    cR
    wf1o
    #
    com
    @20
    cR
    wf1
    #
    @19
    @2
    @21
    @1
    @2
    @20
    com
    wss
    #
    @20
    cfn
    wcel
    #
    wn
    @21
    com
    cP
    difss
    #
    @2
    @24
    com
    cfn
    wcel
    #
    ominf
    @2
    @24
    @26
    @2
    @24
    wa
    com
    cP
    @20
    cun
    #
    cfn
    cP
    com
    wss
    #
    @27
    com
    wceq
    cP
    @9
    vv
    cv
    #
    @0
    cfv
    #
    wss
    #
    vv
    com
    crab
    com
    fin23lem.b
    @31
    vv
    com
    ssrab2
    eqsstri
    #
    cP
    com
    undif
    mpbi
    cP
    @20
    unfi
    syl5eqelr
    ex
    mtoi
    cR
    @20
    vw
    vx
    fin23lem.d
    fin23lem22
    sylancr
    adantl
    com
    @20
    cR
    f1of1
    @22
    @23
    @19
    @25
    com
    @20
    com
    cR
    f1ss
    mpan2
    3syl
    com
    com
    cvv
    @0
    cR
    f1co
    syldan
    com
    cvv
    cZ
    @3
    f1eq1
    syl5ibrcom
    impr
    @1
    @6
    @13
    @16
    @1
    @6
    wa
    @16
    @13
    com
    cvv
    @12
    wf1
    #
    @1
    cP
    cvv
    @11
    wf1
    #
    com
    cP
    cQ
    wf1
    #
    @33
    @6
    @1
    cP
    cvv
    @11
    wf
    #
    va
    cv
    #
    @11
    cfv
    #
    vb
    cv
    #
    @11
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    cP
    wral
    va
    cP
    wral
    @34
    @36
    @1
    @10
    cvv
    wcel
    #
    vz
    cP
    wral
    @36
    @44
    vz
    cP
    @8
    cvv
    wcel
    @44
    @7
    @0
    fvex
    @8
    @9
    cvv
    difexg
    ax-mp
    rgenw
    vz
    cP
    cvv
    @10
    @11
    @11
    eqid
    #
    fmpt
    mpbi
    a1i
    @1
    @43
    va
    vb
    cP
    cP
    @1
    @37
    cP
    wcel
    #
    @39
    cP
    wcel
    #
    wa
    #
    wa
    #
    @41
    @37
    @0
    cfv
    #
    @9
    cdif
    #
    @39
    @0
    cfv
    #
    @9
    cdif
    #
    wceq
    #
    @42
    @49
    @38
    @51
    @40
    @53
    @46
    @38
    @51
    wceq
    @1
    @47
    vz
    @37
    @10
    @51
    cP
    @11
    vz
    va
    weq
    @8
    @50
    @9
    @7
    @37
    @0
    fveq2
    difeq1d
    @45
    @50
    cvv
    wcel
    @51
    cvv
    wcel
    @37
    @0
    fvex
    @50
    @9
    cvv
    difexg
    ax-mp
    fvmpt
    ad2antrl
    @47
    @40
    @53
    wceq
    @1
    @46
    vz
    @39
    @10
    @53
    cP
    @11
    vz
    vb
    weq
    @8
    @52
    @9
    @7
    @39
    @0
    fveq2
    difeq1d
    @45
    @52
    cvv
    wcel
    @53
    cvv
    wcel
    @39
    @0
    fvex
    @52
    @9
    cvv
    difexg
    ax-mp
    fvmpt
    ad2antll
    eqeq12d
    @49
    @54
    @50
    @52
    wceq
    #
    @42
    @54
    @9
    @51
    cun
    #
    @9
    @53
    cun
    #
    wceq
    @49
    @55
    @51
    @53
    @9
    uneq2
    @49
    @56
    @50
    @57
    @52
    @49
    @9
    @50
    wss
    #
    @56
    @50
    wceq
    @46
    @58
    @1
    @47
    @46
    @37
    com
    wcel
    #
    @58
    @31
    @58
    vv
    @37
    com
    cP
    vv
    va
    weq
    @30
    @50
    @9
    @29
    @37
    @0
    fveq2
    sseq2d
    fin23lem.b
    elrab2
    simprbi
    ad2antrl
    @9
    @50
    undif
    sylib
    @49
    @9
    @52
    wss
    #
    @57
    @52
    wceq
    @47
    @60
    @1
    @46
    @47
    @39
    com
    wcel
    #
    @60
    @31
    @60
    vv
    @39
    com
    cP
    vv
    vb
    weq
    @30
    @52
    @9
    @29
    @39
    @0
    fveq2
    sseq2d
    fin23lem.b
    elrab2
    simprbi
    ad2antll
    @9
    @52
    undif
    sylib
    eqeq12d
    syl5ib
    @48
    @1
    @59
    @61
    wa
    @55
    @42
    wb
    @46
    @59
    @47
    @61
    cP
    com
    @37
    @32
    sseli
    cP
    com
    @39
    @32
    sseli
    anim12i
    com
    cvv
    @37
    @39
    @0
    f1fveq
    sylan2
    sylibd
    sylbid
    ralrimivva
    va
    vb
    cP
    cvv
    @11
    dff13
    sylanbrc
    @28
    @6
    @35
    @32
    @28
    @6
    wa
    com
    cP
    cQ
    wf1o
    @35
    cQ
    cP
    vw
    vx
    fin23lem.c
    fin23lem22
    com
    cP
    cQ
    f1of1
    syl
    mpan
    com
    cP
    cvv
    @11
    cQ
    f1co
    syl2an
    com
    cvv
    cZ
    @12
    f1eq1
    syl5ibrcom
    impr
    jaodan
    mpan2
end
