include "cv.mm"
include "clng.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cab.mm"
include "wa.mm"
include "simpl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "difeq1d.mm"
include "simpr.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "3orbi123d.mm"
include "rabeqbidv.mm"
include "mpt2eq123dva.mm"
include "eqeq2d.mm"
include "sbcie2s.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "eqid.mm"
include "elab4g.mm"

theorem istrkgl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let vf: setvar f
  let vi: setvar i
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vp: setvar p
  let vd: setvar d
  let vg: setvar g
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vj: setvar j
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume istrkg.p: |- P = ( Base ` G )
  assume istrkg.d: |- .- = ( dist ` G )
  assume istrkg.i: |- I = ( Itv ` G )

  disjoint f i
  disjoint f p
  disjoint G f
  disjoint i p
  disjoint G i
  disjoint G p
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint I f
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint I p
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P f
  disjoint P i
  disjoint P p
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- f
  disjoint .- i
  disjoint .- p
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d n
  disjoint d p
  disjoint G d
  disjoint f g
  disjoint f n
  disjoint g i
  disjoint g n
  disjoint g p
  disjoint G g
  disjoint i n
  disjoint n p
  disjoint G n
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a n
  disjoint a p
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b n
  disjoint b p
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c n
  disjoint c p
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint I c
  disjoint d j
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint f j
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint g j
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint I g
  disjoint i j
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint j n
  disjoint j p
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint I n
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint I s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint I t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint I u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P g
  disjoint P j
  disjoint P n
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint .- a
  disjoint .- b
  disjoint .- c
  disjoint .- d
  disjoint .- g
  disjoint .- j
  disjoint .- n
  disjoint .- u
  disjoint .- v
  assert |- ( G e. { f | [. ( Base ` f ) / p ]. [. ( Itv ` f ) / i ]. ( LineG ` f ) = ( x e. p , y e. ( p \ { x } ) |-> { z e. p | ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) } ) } <-> ( G e. _V /\ ( LineG ` G ) = ( x e. P , y e. ( P \ { x } ) |-> { z e. P | ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) } ) ) )

  proof
    vf
    cv
    #
    clng
    cfv
    #
    vx
    vy
    vp
    cv
    #
    @2
    vx
    cv
    #
    csn
    #
    cdif
    #
    vz
    cv
    #
    @3
    vy
    cv
    #
    vi
    cv
    #
    co
    #
    wcel
    #
    @3
    @6
    @7
    @8
    co
    #
    wcel
    #
    @7
    @3
    @6
    @8
    co
    #
    wcel
    #
    w3o
    #
    vz
    @2
    crab
    #
    cmpt2
    #
    wceq
    #
    vi
    @0
    citv
    cfv
    wsbc
    vp
    @0
    cbs
    cfv
    wsbc
    #
    cG
    clng
    cfv
    #
    vx
    vy
    cP
    cP
    @4
    cdif
    #
    @6
    @3
    @7
    cI
    co
    #
    wcel
    #
    @3
    @6
    @7
    cI
    co
    #
    wcel
    #
    @7
    @3
    @6
    cI
    co
    #
    wcel
    #
    w3o
    #
    vz
    cP
    crab
    #
    cmpt2
    #
    wceq
    #
    vf
    cG
    @19
    vf
    cab
    #
    @0
    cG
    wceq
    #
    @19
    @1
    @30
    wceq
    #
    @31
    @34
    @18
    vf
    cP
    cI
    cbs
    citv
    cG
    vp
    vi
    istrkg.p
    istrkg.i
    @2
    cP
    wceq
    #
    @8
    cI
    wceq
    #
    wa
    #
    @30
    @17
    @1
    @37
    vx
    vy
    cP
    @21
    @29
    @2
    @5
    @16
    @37
    @2
    cP
    @35
    @36
    simpl
    eqcomd
    #
    @37
    @3
    cP
    wcel
    #
    wa
    cP
    @2
    @4
    @37
    cP
    @2
    wceq
    @39
    @38
    adantr
    difeq1d
    @37
    @29
    @16
    wceq
    @39
    @7
    @21
    wcel
    wa
    @37
    @28
    @15
    vz
    cP
    @2
    @38
    @37
    @23
    @10
    @25
    @12
    @27
    @14
    @37
    @22
    @9
    @6
    @37
    cI
    @8
    @3
    @7
    @37
    @8
    cI
    @35
    @36
    simpr
    eqcomd
    #
    oveqd
    eleq2d
    @37
    @24
    @11
    @3
    @37
    cI
    @8
    @6
    @7
    @40
    oveqd
    eleq2d
    @37
    @26
    @13
    @7
    @37
    cI
    @8
    @3
    @6
    @40
    oveqd
    eleq2d
    3orbi123d
    rabeqbidv
    adantr
    mpt2eq123dva
    eqeq2d
    sbcie2s
    @33
    @1
    @20
    @30
    @0
    cG
    clng
    fveq2
    eqeq1d
    bitrd
    @32
    eqid
    elab4g
end
