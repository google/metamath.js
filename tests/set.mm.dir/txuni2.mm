include "cxp.mm"
include "cuni.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "eleq2i.mm"
include "eluni2.mm"
include "bitri.mm"
include "anbi12i.mm"
include "opelxp.mm"
include "reeanv.mm"
include "3bitr4i.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "vex.mm"
include "xpex.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "cmpt2.mm"
include "crn.mm"
include "cab.mm"
include "rnmpt2.mm"
include "eqtri.mm"
include "elab2.mm"
include "sylibr.mm"
include "elssuni.mm"
include "syl.mm"
include "sseld.mm"
include "syl5bir.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "relssi.mm"
include "cpw.mm"
include "wf.mm"
include "wral.mm"
include "syl6sseqr.mm"
include "xpss12.mm"
include "syl2an.mm"
include "elpw.mm"
include "rgen2.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "frn.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "sspwuni.mm"
include "eqssi.mm"

theorem txuni2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  assume txval.1: |- B = ran ( x e. R , y e. S |-> ( x X. y ) )
  assume txuni2.1: |- X = U. R
  assume txuni2.2: |- Y = U. S

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a p
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint R a
  disjoint b c
  disjoint b d
  disjoint b p
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c p
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d p
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint R p
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint R t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S p
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S z
  disjoint a w
  disjoint B a
  disjoint b w
  disjoint B b
  disjoint c w
  disjoint B c
  disjoint d w
  disjoint B d
  disjoint p w
  disjoint B p
  disjoint r w
  disjoint B r
  disjoint s w
  disjoint B s
  disjoint t w
  disjoint B t
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint X w
  disjoint X z
  disjoint Y w
  disjoint Y z
  assert |- ( X X. Y ) = U. B

  proof
    cX
    cY
    cxp
    #
    cB
    cuni
    #
    vz
    vw
    @0
    @1
    cX
    cY
    relxp
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @0
    wcel
    #
    @2
    vr
    cv
    #
    wcel
    #
    @3
    vs
    cv
    #
    wcel
    #
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    #
    @4
    @1
    wcel
    #
    @2
    cX
    wcel
    #
    @3
    cY
    wcel
    #
    wa
    @7
    vr
    cR
    wrex
    #
    @9
    vs
    cS
    wrex
    #
    wa
    @5
    @11
    @13
    @15
    @14
    @16
    @13
    @2
    cR
    cuni
    #
    wcel
    @15
    cX
    @17
    @2
    txuni2.1
    eleq2i
    vr
    @2
    cR
    eluni2
    bitri
    @14
    @3
    cS
    cuni
    #
    wcel
    @16
    cY
    @18
    @3
    txuni2.2
    eleq2i
    vs
    @3
    cS
    eluni2
    bitri
    anbi12i
    @2
    @3
    cX
    cY
    opelxp
    @7
    @9
    vr
    vs
    cR
    cS
    reeanv
    3bitr4i
    @10
    @12
    vr
    vs
    cR
    cS
    @10
    @4
    @6
    @8
    cxp
    #
    wcel
    @6
    cR
    wcel
    #
    @8
    cS
    wcel
    #
    wa
    #
    @12
    @2
    @3
    @6
    @8
    opelxp
    @22
    @19
    @1
    @4
    @22
    @19
    cB
    wcel
    #
    @19
    @1
    wss
    @22
    @19
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    wceq
    #
    vy
    cS
    wrex
    vx
    cR
    wrex
    #
    @23
    @20
    @21
    @19
    @19
    wceq
    #
    @28
    @19
    eqid
    @27
    @29
    @19
    @6
    @25
    cxp
    #
    wceq
    vx
    vy
    @6
    @8
    cR
    cS
    @24
    @6
    wceq
    @26
    @30
    @19
    @24
    @6
    @25
    xpeq1
    eqeq2d
    @25
    @8
    wceq
    @30
    @19
    @19
    @25
    @8
    @6
    xpeq2
    eqeq2d
    rspc2ev
    mp3an3
    @2
    @26
    wceq
    #
    vy
    cS
    wrex
    vx
    cR
    wrex
    #
    @28
    vz
    @19
    cB
    @6
    @8
    vr
    vex
    vs
    vex
    xpex
    @2
    @19
    wceq
    @31
    @27
    vx
    vy
    cR
    cS
    @2
    @19
    @26
    eqeq1
    2rexbidv
    cB
    vx
    vy
    cR
    cS
    @26
    cmpt2
    #
    crn
    #
    @32
    vz
    cab
    txval.1
    vx
    vy
    vz
    cR
    cS
    @26
    @33
    @33
    eqid
    #
    rnmpt2
    eqtri
    elab2
    sylibr
    @19
    cB
    elssuni
    syl
    sseld
    syl5bir
    rexlimivv
    sylbi
    relssi
    cB
    @0
    cpw
    #
    wss
    @1
    @0
    wss
    cB
    @34
    @36
    txval.1
    cR
    cS
    cxp
    #
    @36
    @33
    wf
    #
    @34
    @36
    wss
    @26
    @36
    wcel
    #
    vy
    cS
    wral
    vx
    cR
    wral
    @38
    @39
    vx
    vy
    cR
    cS
    @24
    cR
    wcel
    #
    @25
    cS
    wcel
    #
    wa
    @26
    @0
    wss
    #
    @39
    @40
    @24
    cX
    wss
    @25
    cY
    wss
    @42
    @41
    @40
    @24
    @17
    cX
    @24
    cR
    elssuni
    txuni2.1
    syl6sseqr
    @41
    @25
    @18
    cY
    @25
    cS
    elssuni
    txuni2.2
    syl6sseqr
    @24
    cX
    @25
    cY
    xpss12
    syl2an
    @26
    @0
    @24
    @25
    vx
    vex
    vy
    vex
    xpex
    elpw
    sylibr
    rgen2
    vx
    vy
    cR
    cS
    @26
    @36
    @33
    @35
    fmpt2
    mpbi
    @37
    @36
    @33
    frn
    ax-mp
    eqsstri
    cB
    @0
    sspwuni
    mpbi
    eqssi
end
