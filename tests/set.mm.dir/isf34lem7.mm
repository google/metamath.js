include "cfin3.mm"
include "wcel.mm"
include "com.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "wss.mm"
include "wral.mm"
include "w3a.mm"
include "crn.mm"
include "cima.mm"
include "cint.mm"
include "cuni.mm"
include "wfn.mm"
include "isf34lem2.mm"
include "adantr.mm"
include "3adant3.mm"
include "ffn.mm"
include "syl.mm"
include "imassrn.mm"
include "wa.mm"
include "frn.mm"
include "syl5ss.mm"
include "ccom.mm"
include "simp1.mm"
include "fco.mm"
include "sylan.mm"
include "cdif.mm"
include "sscon.mm"
include "wceq.mm"
include "simpr.mm"
include "peano2.mm"
include "fvco3.mm"
include "syl2an.mm"
include "simpll.mm"
include "ffvelrn.mm"
include "elpwid.mm"
include "isf34lem1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "adantll.mm"
include "sseq12d.mm"
include "syl5ibr.mm"
include "ralimdva.mm"
include "3impia.mm"
include "fin33i.mm"
include "syl3anc.mm"
include "rnco2.mm"
include "inteqi.mm"
include "3eltr3g.mm"
include "fnfvima.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "cdm.mm"
include "cin.mm"
include "incom.mm"
include "adantl.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "peano1.mm"
include "ne0i.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "imadisj.mm"
include "sylibr.mm"
include "isf34lem5.mm"
include "syl12anc.mm"
include "isf34lem3.mm"
include "unieqd.mm"
include "eleq12d.mm"
include "mpbid.mm"

theorem isf34lem7
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let cX: class X
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F y
  disjoint G y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  assert |- ( ( A e. Fin3 /\ G : _om --> ~P A /\ A. y e. _om ( G ` y ) C_ ( G ` suc y ) ) -> U. ran G e. ran G )

  proof
    cA
    cfin3
    wcel
    #
    com
    cA
    cpw
    #
    cG
    wf
    #
    vy
    cv
    #
    cG
    cfv
    #
    @3
    csuc
    #
    cG
    cfv
    #
    wss
    #
    vy
    com
    wral
    #
    w3a
    #
    cF
    cG
    crn
    #
    cima
    #
    cint
    #
    cF
    cfv
    #
    cF
    @11
    cima
    #
    wcel
    #
    @10
    cuni
    #
    @10
    wcel
    #
    @9
    cF
    @1
    wfn
    #
    @11
    @1
    wss
    #
    @12
    @11
    wcel
    @15
    @9
    @1
    @1
    cF
    wf
    #
    @18
    @0
    @2
    @20
    @8
    @0
    @20
    @2
    vx
    cA
    cF
    cfin3
    compss.a
    isf34lem2
    #
    adantr
    #
    3adant3
    @1
    @1
    cF
    ffn
    syl
    @9
    @11
    cF
    crn
    #
    @1
    cF
    @10
    imassrn
    #
    @0
    @2
    @23
    @1
    wss
    #
    @8
    @0
    @2
    wa
    #
    @20
    @25
    @22
    @1
    @1
    cF
    frn
    syl
    #
    3adant3
    syl5ss
    @9
    cF
    cG
    ccom
    #
    crn
    #
    cint
    #
    @29
    @12
    @11
    @9
    @0
    com
    @1
    @28
    wf
    #
    @5
    @28
    cfv
    #
    @3
    @28
    cfv
    #
    wss
    #
    vy
    com
    wral
    #
    @30
    @29
    wcel
    @0
    @2
    @8
    simp1
    @0
    @2
    @31
    @8
    @0
    @20
    @2
    @31
    @21
    com
    @1
    @1
    cF
    cG
    fco
    sylan
    3adant3
    @0
    @2
    @8
    @35
    @26
    @7
    @34
    vy
    com
    @7
    @34
    @26
    @3
    com
    wcel
    #
    wa
    #
    cA
    @6
    cdif
    #
    cA
    @4
    cdif
    #
    wss
    @4
    @6
    cA
    sscon
    @37
    @32
    @38
    @33
    @39
    @37
    @32
    @6
    cF
    cfv
    #
    @38
    @26
    @2
    @5
    com
    wcel
    #
    @32
    @40
    wceq
    @36
    @0
    @2
    simpr
    #
    @3
    peano2
    #
    com
    @1
    @5
    cF
    cG
    fvco3
    syl2an
    @37
    @0
    @6
    cA
    wss
    @40
    @38
    wceq
    @0
    @2
    @36
    simpll
    #
    @37
    @6
    cA
    @26
    @2
    @41
    @6
    @1
    wcel
    @36
    @42
    @43
    com
    @1
    @5
    cG
    ffvelrn
    syl2an
    elpwid
    vx
    cA
    cF
    cfin3
    @6
    compss.a
    isf34lem1
    syl2anc
    eqtrd
    @37
    @33
    @4
    cF
    cfv
    #
    @39
    @2
    @36
    @33
    @45
    wceq
    @0
    com
    @1
    @3
    cF
    cG
    fvco3
    adantll
    @37
    @0
    @4
    cA
    wss
    @45
    @39
    wceq
    @44
    @37
    @4
    cA
    @2
    @36
    @4
    @1
    wcel
    @0
    com
    @1
    @3
    cG
    ffvelrn
    adantll
    elpwid
    vx
    cA
    cF
    cfin3
    @4
    compss.a
    isf34lem1
    syl2anc
    eqtrd
    sseq12d
    syl5ibr
    ralimdva
    3impia
    vy
    cA
    @28
    fin33i
    syl3anc
    @29
    @11
    cF
    cG
    rnco2
    #
    inteqi
    @46
    3eltr3g
    @1
    @11
    cF
    @12
    fnfvima
    syl3anc
    @0
    @2
    @15
    @17
    wb
    @8
    @26
    @13
    @16
    @14
    @10
    @26
    @13
    @14
    cuni
    #
    @16
    @26
    @0
    @19
    @11
    c0
    wne
    #
    @13
    @47
    wceq
    @0
    @2
    simpl
    #
    @26
    @11
    @23
    @1
    @24
    @27
    syl5ss
    @26
    cF
    cdm
    #
    @10
    cin
    #
    c0
    wne
    @48
    @26
    @51
    @10
    c0
    @26
    @51
    @10
    @50
    cin
    #
    @10
    @50
    @10
    incom
    @26
    @10
    @50
    wss
    @52
    @10
    wceq
    @26
    @10
    @1
    @50
    @2
    @10
    @1
    wss
    #
    @0
    com
    @1
    cG
    frn
    adantl
    #
    @26
    @20
    @50
    @1
    wceq
    @22
    @1
    @1
    cF
    fdm
    syl
    sseqtr4d
    @10
    @50
    df-ss
    sylib
    syl5eq
    @26
    cG
    cdm
    #
    c0
    wne
    @10
    c0
    wne
    @26
    @55
    com
    c0
    @2
    @55
    com
    wceq
    @0
    com
    @1
    cG
    fdm
    adantl
    c0
    com
    wcel
    com
    c0
    wne
    @26
    peano1
    com
    c0
    ne0i
    mp1i
    eqnetrd
    @55
    c0
    @10
    c0
    cG
    dm0rn0
    necon3bii
    sylib
    eqnetrd
    @11
    c0
    @51
    c0
    cF
    @10
    imadisj
    necon3bii
    sylibr
    vx
    cA
    cF
    cfin3
    @11
    compss.a
    isf34lem5
    syl12anc
    @26
    @14
    @10
    @26
    @0
    @53
    @14
    @10
    wceq
    @49
    @54
    vx
    cA
    cF
    cfin3
    @10
    compss.a
    isf34lem3
    syl2anc
    #
    unieqd
    eqtrd
    @56
    eleq12d
    3adant3
    mpbid
end
