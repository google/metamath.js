include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "citv.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cstrkge.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "simp-6r.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "ad2antrr.mm"
include "3anbi123d.mm"
include "rexeqbidva.mm"
include "imbi12d.mm"
include "raleqbidva.mm"
include "sbcie2s.mm"
include "df-trkge.mm"
include "elab4g.mm"

theorem istrkge
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vp: setvar p
  let vc: setvar c
  let vj: setvar j
  let vs: setvar s
  let vt: setvar t
  assume istrkg.p: |- P = ( Base ` G )
  assume istrkg.d: |- .- = ( dist ` G )
  assume istrkg.i: |- I = ( Itv ` G )

  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint I u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P a
  disjoint P b
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- a
  disjoint .- b
  disjoint .- u
  disjoint .- v
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
  disjoint .- c
  disjoint .- d
  disjoint .- f
  disjoint .- g
  disjoint .- i
  disjoint .- j
  disjoint .- n
  disjoint .- p
  assert |- ( G e. TarskiGE <-> ( G e. _V /\ A. x e. P A. y e. P A. z e. P A. u e. P A. v e. P ( ( u e. ( x I v ) /\ u e. ( y I z ) /\ x =/= u ) -> E. a e. P E. b e. P ( y e. ( x I a ) /\ z e. ( x I b ) /\ v e. ( a I b ) ) ) ) )

  proof
    vu
    cv
    #
    vx
    cv
    #
    vv
    cv
    #
    vi
    cv
    #
    co
    #
    wcel
    #
    @0
    vy
    cv
    #
    vz
    cv
    #
    @3
    co
    #
    wcel
    #
    @1
    @0
    wne
    #
    w3a
    #
    @6
    @1
    va
    cv
    #
    @3
    co
    #
    wcel
    #
    @7
    @1
    vb
    cv
    #
    @3
    co
    #
    wcel
    #
    @2
    @12
    @15
    @3
    co
    #
    wcel
    #
    w3a
    #
    vb
    vp
    cv
    #
    wrex
    #
    va
    @21
    wrex
    #
    wi
    #
    vv
    @21
    wral
    #
    vu
    @21
    wral
    #
    vz
    @21
    wral
    #
    vy
    @21
    wral
    #
    vx
    @21
    wral
    #
    vi
    vf
    cv
    #
    citv
    cfv
    wsbc
    vp
    @30
    cbs
    cfv
    wsbc
    @0
    @1
    @2
    cI
    co
    #
    wcel
    #
    @0
    @6
    @7
    cI
    co
    #
    wcel
    #
    @10
    w3a
    #
    @6
    @1
    @12
    cI
    co
    #
    wcel
    #
    @7
    @1
    @15
    cI
    co
    #
    wcel
    #
    @2
    @12
    @15
    cI
    co
    #
    wcel
    #
    w3a
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    #
    vu
    cP
    wral
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
    vf
    cG
    cstrkge
    @50
    @29
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
    @21
    cP
    wceq
    #
    @3
    cI
    wceq
    #
    wa
    #
    @49
    @28
    vx
    cP
    @21
    @53
    @21
    cP
    @51
    @52
    simpl
    eqcomd
    #
    @53
    @1
    cP
    wcel
    #
    wa
    #
    @48
    @27
    vy
    cP
    @21
    @53
    cP
    @21
    wceq
    #
    @55
    @54
    adantr
    #
    @56
    @6
    cP
    wcel
    #
    wa
    #
    @47
    @26
    vz
    cP
    @21
    @56
    @57
    @59
    @58
    adantr
    #
    @60
    @7
    cP
    wcel
    #
    wa
    #
    @46
    @25
    vu
    cP
    @21
    @60
    @57
    @62
    @61
    adantr
    #
    @63
    @0
    cP
    wcel
    #
    wa
    #
    @45
    @24
    vv
    cP
    @21
    @63
    @57
    @65
    @64
    adantr
    #
    @66
    @2
    cP
    wcel
    #
    wa
    #
    @35
    @11
    @44
    @23
    @69
    @32
    @5
    @34
    @9
    @10
    @69
    @31
    @4
    @0
    @69
    cI
    @3
    @1
    @2
    @69
    @3
    cI
    @51
    @52
    @55
    @59
    @62
    @65
    @68
    simp-6r
    #
    eqcomd
    #
    oveqd
    eleq2d
    @69
    @33
    @8
    @0
    @69
    cI
    @3
    @6
    @7
    @71
    oveqd
    eleq2d
    3anbi12d
    @69
    @43
    @22
    va
    cP
    @21
    @66
    @57
    @68
    @67
    adantr
    #
    @69
    @12
    cP
    wcel
    #
    wa
    #
    @42
    @20
    vb
    cP
    @21
    @69
    @57
    @73
    @72
    adantr
    @74
    @15
    cP
    wcel
    #
    wa
    #
    @37
    @14
    @39
    @17
    @41
    @19
    @76
    @36
    @13
    @6
    @76
    cI
    @3
    @1
    @12
    @76
    @3
    cI
    @69
    @52
    @73
    @75
    @70
    ad2antrr
    eqcomd
    #
    oveqd
    eleq2d
    @76
    @38
    @16
    @7
    @76
    cI
    @3
    @1
    @15
    @77
    oveqd
    eleq2d
    @76
    @40
    @18
    @2
    @76
    cI
    @3
    @12
    @15
    @77
    oveqd
    eleq2d
    3anbi123d
    rexeqbidva
    rexeqbidva
    imbi12d
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    sbcie2s
    vx
    vy
    vz
    vv
    vu
    vf
    vi
    vp
    va
    vb
    df-trkge
    elab4g
end
