include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cima.mm"
include "cuni.mm"
include "cfv.mm"
include "cint.mm"
include "wceq.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "isf34lem2.mm"
include "adantr.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "cdm.mm"
include "cin.mm"
include "simprl.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "simprr.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "jca.mm"
include "isf34lem4.mm"
include "syldan.mm"
include "isf34lem3.mm"
include "adantrr.mm"
include "inteqd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "ccnv.mm"
include "compsscnv.mm"
include "fveq1i.mm"
include "wf1o.mm"
include "crpss.mm"
include "wiso.mm"
include "compssiso.mm"
include "isof1o.mm"
include "sspwuni.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "f1ocnvfv1.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"

theorem isf34lem5
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint A x
  disjoint V x
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
  disjoint x y
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( ( A e. V /\ ( X C_ ~P A /\ X =/= (/) ) ) -> ( F ` |^| X ) = U. ( F " X ) )

  proof
    cA
    cV
    wcel
    #
    cX
    cA
    cpw
    #
    wss
    #
    cX
    c0
    wne
    #
    wa
    #
    wa
    #
    cF
    cX
    cima
    #
    cuni
    #
    cF
    cfv
    #
    cF
    cfv
    #
    cX
    cint
    #
    cF
    cfv
    @7
    @5
    @8
    @10
    cF
    @5
    @8
    cF
    @6
    cima
    #
    cint
    #
    @10
    @0
    @4
    @6
    @1
    wss
    #
    @6
    c0
    wne
    #
    wa
    @8
    @12
    wceq
    @5
    @13
    @14
    @5
    @6
    cF
    crn
    #
    @1
    cF
    cX
    imassrn
    @5
    @1
    @1
    cF
    wf
    #
    @15
    @1
    wss
    @0
    @16
    @4
    vx
    cA
    cF
    cV
    compss.a
    isf34lem2
    adantr
    #
    @1
    @1
    cF
    frn
    syl
    syl5ss
    #
    @5
    cF
    cdm
    #
    cX
    cin
    #
    c0
    wne
    @14
    @5
    @20
    cX
    c0
    @5
    cX
    @19
    wss
    @20
    cX
    wceq
    @5
    cX
    @1
    @19
    @0
    @2
    @3
    simprl
    @5
    @16
    @19
    @1
    wceq
    @17
    @1
    @1
    cF
    fdm
    syl
    sseqtr4d
    cX
    @19
    sseqin2
    sylib
    @0
    @2
    @3
    simprr
    eqnetrd
    @6
    c0
    @20
    c0
    cF
    cX
    imadisj
    necon3bii
    sylibr
    jca
    vx
    cA
    cF
    cV
    @6
    compss.a
    isf34lem4
    syldan
    @5
    @11
    cX
    @0
    @2
    @11
    cX
    wceq
    @3
    vx
    cA
    cF
    cV
    cX
    compss.a
    isf34lem3
    adantrr
    inteqd
    eqtrd
    fveq2d
    @5
    @9
    @8
    cF
    ccnv
    #
    cfv
    #
    @7
    @8
    @21
    cF
    vx
    cA
    cF
    compss.a
    compsscnv
    fveq1i
    @5
    @1
    @1
    cF
    wf1o
    #
    @7
    @1
    wcel
    #
    @22
    @7
    wceq
    @0
    @23
    @4
    @0
    @1
    @1
    crpss
    crpss
    ccnv
    #
    cF
    wiso
    @23
    vx
    cA
    cF
    cV
    compss.a
    compssiso
    @1
    @1
    crpss
    @25
    cF
    isof1o
    syl
    adantr
    @5
    @24
    @7
    cA
    wss
    #
    @5
    @13
    @26
    @18
    @6
    cA
    sspwuni
    sylib
    @0
    @24
    @26
    wb
    @4
    @7
    cA
    cV
    elpw2g
    adantr
    mpbird
    @1
    @1
    @7
    cF
    f1ocnvfv1
    syl2anc
    syl5eqr
    eqtr3d
end
