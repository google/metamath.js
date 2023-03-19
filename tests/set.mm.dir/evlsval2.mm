include "wcel.mm"
include "ccrg.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "crh.mm"
include "co.mm"
include "crab.mm"
include "crio.mm"
include "evlsval.mm"
include "wreu.mm"
include "cbs.mm"
include "eqid.mm"
include "cvv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "subrgcrng.mm"
include "3adant1.mm"
include "cmap.mm"
include "simp2.mm"
include "ovex.mm"
include "pwscrng.mm"
include "sylancl.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cres.mm"
include "wss.mm"
include "subrgss.mm"
include "3ad2ant3.mm"
include "resmptd.mm"
include "syl6eqr.mm"
include "crg.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "pwsdiagrhm.mm"
include "simp3.mm"
include "resrhm.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "wf.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simpl1.mm"
include "elmapg.mm"
include "sylancr.mm"
include "biimpa.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "simpl2.mm"
include "pwselbasb.mm"
include "mpbird.mm"
include "evlseu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylib.mm"

theorem evlsval2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vm: setvar m
  assume evlsval.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlsval.w: |- W = ( I mPoly U )
  assume evlsval.v: |- V = ( I mVar U )
  assume evlsval.u: |- U = ( S |`s R )
  assume evlsval.t: |- T = ( S ^s ( B ^m I ) )
  assume evlsval.b: |- B = ( Base ` S )
  assume evlsval.a: |- A = ( algSc ` W )
  assume evlsval.x: |- X = ( x e. R |-> ( ( B ^m I ) X. { x } ) )
  assume evlsval.y: |- Y = ( x e. I |-> ( g e. ( B ^m I ) |-> ( g ` x ) ) )

  disjoint I g
  disjoint I x
  disjoint g x
  disjoint R x
  disjoint S g
  disjoint S x
  disjoint B g
  disjoint B x
  disjoint R g
  disjoint T x
  disjoint Z g
  disjoint Z x
  disjoint I b
  disjoint I f
  disjoint I i
  disjoint I r
  disjoint I s
  disjoint I w
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b r
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint f g
  disjoint f i
  disjoint f r
  disjoint f s
  disjoint f w
  disjoint f x
  disjoint g i
  disjoint g r
  disjoint g s
  disjoint g w
  disjoint i r
  disjoint i s
  disjoint i w
  disjoint i x
  disjoint r s
  disjoint r w
  disjoint r x
  disjoint s w
  disjoint s x
  disjoint w x
  disjoint R f
  disjoint R r
  disjoint S b
  disjoint S f
  disjoint S i
  disjoint S r
  disjoint S s
  disjoint S w
  disjoint T f
  disjoint W f
  disjoint A m
  disjoint I m
  disjoint Q m
  disjoint R m
  disjoint g m
  disjoint S m
  disjoint T m
  disjoint m x
  disjoint V m
  disjoint W m
  disjoint X m
  disjoint Y m
  disjoint Z m
  assert |- ( ( I e. Z /\ S e. CRing /\ R e. ( SubRing ` S ) ) -> ( Q e. ( W RingHom T ) /\ ( ( Q o. A ) = X /\ ( Q o. V ) = Y ) ) )

  proof
    cI
    cZ
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    #
    w3a
    #
    cQ
    vm
    cv
    #
    cA
    ccom
    #
    cX
    wceq
    #
    @4
    cV
    ccom
    #
    cY
    wceq
    #
    wa
    #
    vm
    cW
    cT
    crh
    co
    #
    crab
    #
    wcel
    cQ
    @10
    wcel
    cQ
    cA
    ccom
    #
    cX
    wceq
    #
    cQ
    cV
    ccom
    #
    cY
    wceq
    #
    wa
    #
    wa
    @3
    cQ
    @9
    vm
    @10
    crio
    #
    @11
    vx
    cA
    cB
    cQ
    cR
    cS
    cT
    cU
    vm
    vg
    cI
    cV
    cW
    cX
    cY
    cZ
    evlsval.q
    evlsval.w
    evlsval.v
    evlsval.u
    evlsval.t
    evlsval.b
    evlsval.a
    evlsval.x
    evlsval.y
    evlsval
    @3
    @9
    vm
    @10
    wreu
    @17
    @11
    wcel
    @3
    cA
    cT
    cbs
    cfv
    #
    cW
    cU
    cT
    vm
    cX
    cY
    cI
    cV
    evlsval.w
    @18
    eqid
    #
    evlsval.a
    evlsval.v
    @0
    @1
    cI
    cvv
    wcel
    @2
    cI
    cZ
    elex
    3ad2ant1
    @1
    @2
    cU
    ccrg
    wcel
    @0
    cR
    cS
    cU
    evlsval.u
    subrgcrng
    3adant1
    @3
    @1
    cB
    cI
    cmap
    co
    #
    cvv
    wcel
    #
    cT
    ccrg
    wcel
    @0
    @1
    @2
    simp2
    cB
    cI
    cmap
    ovex
    #
    cS
    @20
    cvv
    cT
    evlsval.t
    pwscrng
    sylancl
    @3
    vx
    cB
    @20
    vx
    cv
    #
    csn
    cxp
    #
    cmpt
    #
    cR
    cres
    #
    cX
    cU
    cT
    crh
    co
    #
    @3
    @26
    vx
    cR
    @24
    cmpt
    cX
    @3
    vx
    cB
    cR
    @24
    @2
    @0
    cR
    cB
    wss
    @1
    cR
    cB
    cS
    evlsval.b
    subrgss
    3ad2ant3
    resmptd
    evlsval.x
    syl6eqr
    @3
    @25
    cS
    cT
    crh
    co
    wcel
    #
    @2
    @26
    @27
    wcel
    @3
    cS
    crg
    wcel
    #
    @21
    @28
    @1
    @0
    @29
    @2
    cS
    crngring
    3ad2ant2
    @22
    vx
    cB
    cS
    @25
    @20
    cvv
    cT
    evlsval.t
    evlsval.b
    @25
    eqid
    pwsdiagrhm
    sylancl
    @0
    @1
    @2
    simp3
    cS
    cT
    cU
    @25
    cR
    evlsval.u
    resrhm
    syl2anc
    eqeltrrd
    @3
    vx
    cI
    vg
    @20
    @23
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    @18
    cY
    @3
    @23
    cI
    wcel
    #
    wa
    #
    @32
    @18
    wcel
    #
    @20
    cB
    @32
    wf
    #
    @34
    vg
    @20
    @31
    cB
    @32
    @34
    @30
    @20
    wcel
    #
    wa
    cI
    cB
    @23
    @30
    @34
    @37
    cI
    cB
    @30
    wf
    #
    @34
    cB
    cvv
    wcel
    @0
    @37
    @38
    wb
    cB
    cS
    cbs
    cfv
    cvv
    evlsval.b
    cS
    cbs
    fvex
    eqeltri
    @0
    @1
    @2
    @33
    simpl1
    cB
    cI
    @30
    cvv
    cZ
    elmapg
    sylancr
    biimpa
    @3
    @33
    @37
    simplr
    ffvelrnd
    @32
    eqid
    fmptd
    @34
    @1
    @21
    @35
    @36
    wb
    @0
    @1
    @2
    @33
    simpl2
    @22
    cB
    cS
    @20
    @18
    ccrg
    @32
    cT
    cvv
    evlsval.t
    evlsval.b
    @19
    pwselbasb
    sylancl
    mpbird
    evlsval.y
    fmptd
    evlseu
    @9
    vm
    @10
    riotacl2
    syl
    eqeltrd
    @9
    @16
    vm
    cQ
    @10
    @4
    cQ
    wceq
    #
    @6
    @13
    @8
    @15
    @39
    @5
    @12
    cX
    @4
    cQ
    cA
    coeq1
    eqeq1d
    @39
    @7
    @14
    cY
    @4
    cQ
    cV
    coeq1
    eqeq1d
    anbi12d
    elrab
    sylib
end
