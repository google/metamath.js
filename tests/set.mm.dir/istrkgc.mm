include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cstrkgc.mm"
include "simpl.mm"
include "eqcomd.mm"
include "wcel.mm"
include "adantr.mm"
include "simpllr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidva.mm"
include "oveqdr.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "sbcie2s.mm"
include "df-trkgc.mm"
include "elab4g.mm"

theorem istrkgc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vp: setvar p
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

  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
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
  disjoint f i
  disjoint f n
  disjoint f p
  disjoint G f
  disjoint g i
  disjoint g n
  disjoint g p
  disjoint G g
  disjoint i n
  disjoint i p
  disjoint G i
  disjoint n p
  disjoint G n
  disjoint G p
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
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint I f
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
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
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
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint I p
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
  disjoint P f
  disjoint P g
  disjoint P i
  disjoint P j
  disjoint P n
  disjoint P p
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint .- a
  disjoint .- b
  disjoint .- c
  disjoint .- d
  disjoint .- f
  disjoint .- g
  disjoint .- i
  disjoint .- j
  disjoint .- n
  disjoint .- p
  disjoint .- u
  disjoint .- v
  assert |- ( G e. TarskiGC <-> ( G e. _V /\ ( A. x e. P A. y e. P ( x .- y ) = ( y .- x ) /\ A. x e. P A. y e. P A. z e. P ( ( x .- y ) = ( z .- z ) -> x = y ) ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vd
    cv
    #
    co
    #
    @1
    @0
    @2
    co
    #
    wceq
    #
    vy
    vp
    cv
    #
    wral
    #
    vx
    @6
    wral
    #
    @3
    vz
    cv
    #
    @9
    @2
    co
    #
    wceq
    #
    @0
    @1
    wceq
    #
    wi
    #
    vz
    @6
    wral
    #
    vy
    @6
    wral
    #
    vx
    @6
    wral
    #
    wa
    #
    vd
    vf
    cv
    #
    cds
    cfv
    wsbc
    vp
    @18
    cbs
    cfv
    wsbc
    @0
    @1
    c.mi
    co
    #
    @1
    @0
    c.mi
    co
    #
    wceq
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    @19
    @9
    @9
    c.mi
    co
    #
    wceq
    #
    @12
    wi
    #
    vz
    cP
    wral
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    wa
    #
    vf
    cG
    cstrkgc
    @30
    @17
    vf
    cP
    c.mi
    cbs
    cds
    cG
    vp
    vd
    istrkg.p
    istrkg.d
    @6
    cP
    wceq
    #
    @2
    c.mi
    wceq
    #
    wa
    #
    @23
    @8
    @29
    @16
    @33
    @22
    @7
    vx
    cP
    @6
    @33
    @6
    cP
    @31
    @32
    simpl
    eqcomd
    #
    @33
    @0
    cP
    wcel
    #
    wa
    #
    @21
    @5
    vy
    cP
    @6
    @33
    cP
    @6
    wceq
    #
    @35
    @34
    adantr
    #
    @36
    @1
    cP
    wcel
    #
    wa
    #
    @19
    @3
    @20
    @4
    @40
    c.mi
    @2
    @0
    @1
    @40
    @2
    c.mi
    @31
    @32
    @35
    @39
    simpllr
    eqcomd
    #
    oveqd
    @40
    c.mi
    @2
    @1
    @0
    @41
    oveqd
    eqeq12d
    raleqbidva
    raleqbidva
    @33
    @28
    @15
    vx
    cP
    @6
    @34
    @36
    @27
    @14
    vy
    cP
    @6
    @38
    @40
    @26
    @13
    vz
    cP
    @6
    @36
    @37
    @39
    @38
    adantr
    @40
    @9
    cP
    wcel
    #
    wa
    #
    @25
    @11
    @12
    @43
    @19
    @3
    @24
    @10
    @40
    @42
    vx
    vy
    c.mi
    @2
    @41
    oveqdr
    @40
    @42
    vz
    vz
    c.mi
    @2
    @41
    oveqdr
    eqeq12d
    imbi1d
    raleqbidva
    raleqbidva
    raleqbidva
    anbi12d
    sbcie2s
    vx
    vy
    vz
    vf
    vp
    vd
    df-trkgc
    elab4g
end
