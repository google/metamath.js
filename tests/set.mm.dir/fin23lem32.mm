include "wcel.mm"
include "com.mm"
include "cvv.mm"
include "cv.mm"
include "wf1.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wpss.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cmpt.mm"
include "fin23lem28.mm"
include "ad2antrl.mm"
include "simprl.mm"
include "simpl.mm"
include "simprr.mm"
include "fin23lem31.mm"
include "syl3anc.mm"
include "wceq.mm"
include "wb.mm"
include "wf.mm"
include "wfn.mm"
include "f1fn.mm"
include "dffn3.mm"
include "sylib.mm"
include "sspwuni.mm"
include "biimpri.mm"
include "ad2antll.mm"
include "fssd.mm"
include "pwexg.mm"
include "adantr.mm"
include "vex.mm"
include "f1f.mm"
include "dmfex.mm"
include "sylancr.mm"
include "elmapd.mm"
include "mpbird.mm"
include "syl.mm"
include "fex.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "f1eq1.mm"
include "rneq.mm"
include "unieqd.mm"
include "psseq1d.mm"
include "anbi12d.mm"
include "mpbir2and.mm"
include "ex.mm"
include "alrimiv.mm"
include "ovex.mm"
include "mptex.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "rneqd.mm"
include "imbi2d.mm"
include "albid.mm"
include "spcev.mm"
include "sseq1d.mm"
include "fveq2.mm"
include "psseq12d.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "exbii.mm"
include "sylibr.mm"

theorem fin23lem32
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
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  let cB: class B
  let cV: class V
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
  disjoint a b
  disjoint a i
  disjoint a u
  disjoint b i
  disjoint b u
  disjoint a t
  disjoint F a
  disjoint F t
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint P a
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint P b
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint a v
  disjoint R a
  disjoint b v
  disjoint R b
  disjoint R i
  disjoint R u
  disjoint R v
  disjoint U a
  disjoint U b
  disjoint U i
  disjoint U u
  disjoint U v
  disjoint U z
  disjoint a f
  disjoint Z a
  disjoint b f
  disjoint Z b
  disjoint Z f
  disjoint a g
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
  disjoint c g
  disjoint c i
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint A a
  disjoint A b
  disjoint A i
  disjoint A u
  disjoint B a
  disjoint B b
  disjoint V a
  disjoint a c
  disjoint b c
  disjoint U c
  assert |- ( G e. F -> E. f A. b ( ( b : _om -1-1-> _V /\ U. ran b C_ G ) -> ( ( f ` b ) : _om -1-1-> _V /\ U. ran ( f ` b ) C. U. ran b ) ) )

  proof
    cG
    cF
    wcel
    #
    com
    cvv
    vt
    cv
    #
    wf1
    #
    @1
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    com
    cvv
    @1
    vf
    cv
    #
    cfv
    #
    wf1
    #
    @8
    crn
    #
    cuni
    #
    @4
    wpss
    #
    wa
    #
    wi
    #
    vt
    wal
    #
    vf
    wex
    #
    com
    cvv
    vb
    cv
    #
    wf1
    #
    @17
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    com
    cvv
    @17
    @7
    cfv
    #
    wf1
    #
    @23
    crn
    #
    cuni
    #
    @20
    wpss
    #
    wa
    #
    wi
    #
    vb
    wal
    #
    vf
    wex
    @0
    @6
    com
    cvv
    @1
    vt
    cG
    cpw
    #
    com
    cmap
    co
    #
    cZ
    cmpt
    #
    cfv
    #
    wf1
    #
    @34
    crn
    #
    cuni
    #
    @4
    wpss
    #
    wa
    #
    wi
    #
    vt
    wal
    #
    @16
    @0
    @40
    vt
    @0
    @6
    @39
    @0
    @6
    wa
    #
    @39
    com
    cvv
    cZ
    wf1
    #
    cZ
    crn
    #
    cuni
    #
    @4
    wpss
    #
    @2
    @43
    @0
    @5
    vx
    vz
    vw
    vv
    vu
    vt
    cP
    cQ
    cR
    cU
    vg
    vi
    cF
    cZ
    va
    fin23lem.a
    fin23lem17.f
    fin23lem.b
    fin23lem.c
    fin23lem.d
    fin23lem.e
    fin23lem28
    ad2antrl
    #
    @42
    @2
    @0
    @5
    @46
    @0
    @2
    @5
    simprl
    @0
    @6
    simpl
    @0
    @2
    @5
    simprr
    vx
    vz
    vw
    vv
    vu
    vt
    cP
    cQ
    cR
    cU
    vg
    vi
    cF
    cG
    cvv
    cZ
    va
    fin23lem.a
    fin23lem17.f
    fin23lem.b
    fin23lem.c
    fin23lem.d
    fin23lem.e
    fin23lem31
    syl3anc
    @42
    @34
    cZ
    wceq
    #
    @39
    @43
    @46
    wa
    wb
    @42
    @1
    @32
    wcel
    #
    cZ
    cvv
    wcel
    #
    @48
    @42
    @49
    com
    @31
    @1
    wf
    @42
    com
    @3
    @31
    @1
    @2
    com
    @3
    @1
    wf
    #
    @0
    @5
    @2
    @1
    com
    wfn
    @51
    com
    cvv
    @1
    f1fn
    com
    @1
    dffn3
    sylib
    ad2antrl
    @5
    @3
    @31
    wss
    #
    @0
    @2
    @52
    @5
    @3
    cG
    sspwuni
    biimpri
    ad2antll
    fssd
    @42
    @31
    com
    @1
    cvv
    cvv
    @0
    @31
    cvv
    wcel
    @6
    cG
    cF
    pwexg
    adantr
    @2
    com
    cvv
    wcel
    #
    @0
    @5
    @2
    @1
    cvv
    wcel
    com
    cvv
    @1
    wf
    @53
    vt
    vex
    com
    cvv
    @1
    f1f
    com
    cvv
    cvv
    @1
    dmfex
    sylancr
    ad2antrl
    #
    elmapd
    mpbird
    @42
    com
    cvv
    cZ
    wf
    #
    @53
    @50
    @42
    @43
    @55
    @47
    com
    cvv
    cZ
    f1f
    syl
    @54
    com
    cvv
    cvv
    cZ
    fex
    syl2anc
    vt
    @32
    cZ
    cvv
    @33
    @33
    eqid
    fvmpt2
    syl2anc
    @48
    @35
    @43
    @38
    @46
    com
    cvv
    @34
    cZ
    f1eq1
    @48
    @37
    @45
    @4
    @48
    @36
    @44
    @34
    cZ
    rneq
    unieqd
    psseq1d
    anbi12d
    syl
    mpbir2and
    ex
    alrimiv
    @15
    @41
    vf
    @33
    vt
    @32
    cZ
    @31
    com
    cmap
    ovex
    mptex
    @7
    @33
    wceq
    #
    @14
    @40
    vt
    vt
    @7
    @33
    vt
    @32
    cZ
    nfmpt1
    nfeq2
    @56
    @13
    @39
    @6
    @56
    @9
    @35
    @12
    @38
    @56
    @8
    @34
    wceq
    @9
    @35
    wb
    @1
    @7
    @33
    fveq1
    #
    com
    cvv
    @8
    @34
    f1eq1
    syl
    @56
    @11
    @37
    @4
    @56
    @10
    @36
    @56
    @8
    @34
    @57
    rneqd
    unieqd
    psseq1d
    anbi12d
    imbi2d
    albid
    spcev
    syl
    @30
    @15
    vf
    @29
    @14
    vb
    vt
    @17
    @1
    wceq
    #
    @22
    @6
    @28
    @13
    @58
    @18
    @2
    @21
    @5
    com
    cvv
    @17
    @1
    f1eq1
    @58
    @20
    @4
    cG
    @58
    @19
    @3
    @17
    @1
    rneq
    unieqd
    #
    sseq1d
    anbi12d
    @58
    @24
    @9
    @27
    @12
    @58
    @23
    @8
    wceq
    @24
    @9
    wb
    @17
    @1
    @7
    fveq2
    #
    com
    cvv
    @23
    @8
    f1eq1
    syl
    @58
    @26
    @11
    @20
    @4
    @58
    @25
    @10
    @58
    @23
    @8
    @60
    rneqd
    unieqd
    @59
    psseq12d
    anbi12d
    imbi12d
    cbvalv
    exbii
    sylibr
end
