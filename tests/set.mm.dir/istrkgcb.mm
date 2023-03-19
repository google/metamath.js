include "cv.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "citv.mm"
include "cfv.mm"
include "wsbc.mm"
include "cds.mm"
include "cbs.mm"
include "cstrkgcb.mm"
include "simp1.mm"
include "eqcomd.mm"
include "adantr.mm"
include "ad6antr.mm"
include "simpll3.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "3anbi23d.mm"
include "simpll2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "raleqbidva.mm"
include "ad3antrrr.mm"
include "rexeqbidva.mm"
include "sbcie3s.mm"
include "df-trkgcb.mm"
include "elab4g.mm"

theorem istrkgcb
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
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vp: setvar p
  let vj: setvar j
  let vs: setvar s
  let vt: setvar t
  assume istrkg.p: |- P = ( Base ` G )
  assume istrkg.d: |- .- = ( dist ` G )
  assume istrkg.i: |- I = ( Itv ` G )

  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint I c
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
  disjoint P c
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- a
  disjoint .- b
  disjoint .- c
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
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a n
  disjoint a p
  disjoint a s
  disjoint a t
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
  disjoint P d
  disjoint P f
  disjoint P g
  disjoint P i
  disjoint P j
  disjoint P n
  disjoint P p
  disjoint P s
  disjoint P t
  disjoint .- d
  disjoint .- f
  disjoint .- g
  disjoint .- i
  disjoint .- j
  disjoint .- n
  disjoint .- p
  assert |- ( G e. TarskiGCB <-> ( G e. _V /\ ( A. x e. P A. y e. P A. z e. P A. u e. P A. a e. P A. b e. P A. c e. P A. v e. P ( ( ( x =/= y /\ y e. ( x I z ) /\ b e. ( a I c ) ) /\ ( ( ( x .- y ) = ( a .- b ) /\ ( y .- z ) = ( b .- c ) ) /\ ( ( x .- u ) = ( a .- v ) /\ ( y .- u ) = ( b .- v ) ) ) ) -> ( z .- u ) = ( c .- v ) ) /\ A. x e. P A. y e. P A. a e. P A. b e. P E. z e. P ( y e. ( x I z ) /\ ( y .- z ) = ( a .- b ) ) ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @1
    @0
    vz
    cv
    #
    vi
    cv
    #
    co
    #
    wcel
    #
    vb
    cv
    #
    va
    cv
    #
    vc
    cv
    #
    @4
    co
    #
    wcel
    #
    w3a
    #
    @0
    @1
    vd
    cv
    #
    co
    #
    @8
    @7
    @13
    co
    #
    wceq
    #
    @1
    @3
    @13
    co
    #
    @7
    @9
    @13
    co
    #
    wceq
    #
    wa
    #
    @0
    vu
    cv
    #
    @13
    co
    #
    @8
    vv
    cv
    #
    @13
    co
    #
    wceq
    #
    @1
    @21
    @13
    co
    #
    @7
    @23
    @13
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @3
    @21
    @13
    co
    #
    @9
    @23
    @13
    co
    #
    wceq
    #
    wi
    #
    vv
    vp
    cv
    #
    wral
    #
    vc
    @36
    wral
    #
    vb
    @36
    wral
    #
    va
    @36
    wral
    #
    vu
    @36
    wral
    #
    vz
    @36
    wral
    #
    vy
    @36
    wral
    #
    vx
    @36
    wral
    #
    @6
    @17
    @15
    wceq
    #
    wa
    #
    vz
    @36
    wrex
    #
    vb
    @36
    wral
    #
    va
    @36
    wral
    #
    vy
    @36
    wral
    #
    vx
    @36
    wral
    #
    wa
    #
    vi
    vf
    cv
    #
    citv
    cfv
    wsbc
    vd
    @53
    cds
    cfv
    wsbc
    vp
    @53
    cbs
    cfv
    wsbc
    @2
    @1
    @0
    @3
    cI
    co
    #
    wcel
    #
    @7
    @8
    @9
    cI
    co
    #
    wcel
    #
    w3a
    #
    @0
    @1
    c.mi
    co
    #
    @8
    @7
    c.mi
    co
    #
    wceq
    #
    @1
    @3
    c.mi
    co
    #
    @7
    @9
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @0
    @21
    c.mi
    co
    #
    @8
    @23
    c.mi
    co
    #
    wceq
    #
    @1
    @21
    c.mi
    co
    #
    @7
    @23
    c.mi
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @3
    @21
    c.mi
    co
    #
    @9
    @23
    c.mi
    co
    #
    wceq
    #
    wi
    #
    vv
    cP
    wral
    #
    vc
    cP
    wral
    #
    vb
    cP
    wral
    #
    va
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
    @55
    @62
    @60
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    vb
    cP
    wral
    #
    va
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
    cstrkgcb
    @94
    @52
    vf
    cP
    c.mi
    cI
    cbs
    cds
    citv
    cG
    vp
    vd
    vi
    istrkg.p
    istrkg.d
    istrkg.i
    @36
    cP
    wceq
    #
    @13
    c.mi
    wceq
    #
    @4
    cI
    wceq
    #
    w3a
    #
    @86
    @44
    @93
    @51
    @98
    @85
    @43
    vx
    cP
    @36
    @98
    @36
    cP
    @95
    @96
    @97
    simp1
    eqcomd
    #
    @98
    @0
    cP
    wcel
    #
    wa
    #
    @84
    @42
    vy
    cP
    @36
    @98
    cP
    @36
    wceq
    #
    @100
    @99
    adantr
    #
    @101
    @1
    cP
    wcel
    #
    wa
    #
    @83
    @41
    vz
    cP
    @36
    @101
    @102
    @104
    @103
    adantr
    #
    @105
    @3
    cP
    wcel
    #
    wa
    #
    @82
    @40
    vu
    cP
    @36
    @105
    @102
    @107
    @106
    adantr
    #
    @108
    @21
    cP
    wcel
    #
    wa
    #
    @81
    @39
    va
    cP
    @36
    @108
    @102
    @110
    @109
    adantr
    #
    @111
    @8
    cP
    wcel
    #
    wa
    #
    @80
    @38
    vb
    cP
    @36
    @111
    @102
    @113
    @112
    adantr
    @114
    @7
    cP
    wcel
    #
    wa
    #
    @79
    @37
    vc
    cP
    @36
    @98
    @102
    @100
    @104
    @107
    @110
    @113
    @115
    @99
    ad6antr
    @116
    @9
    cP
    wcel
    #
    wa
    #
    @78
    @35
    vv
    cP
    @36
    @101
    @102
    @104
    @107
    @110
    @113
    @115
    @117
    @103
    ad6antr
    @118
    @23
    cP
    wcel
    #
    wa
    #
    @74
    @31
    @77
    @34
    @120
    @58
    @12
    @73
    @30
    @120
    @55
    @6
    @57
    @11
    @2
    @120
    @54
    @5
    @1
    @120
    cI
    @4
    @0
    @3
    @120
    @4
    cI
    @105
    @97
    @107
    @110
    @113
    @115
    @117
    @119
    @95
    @96
    @97
    @100
    @104
    simpll3
    #
    ad6antr
    eqcomd
    #
    oveqd
    eleq2d
    @120
    @56
    @10
    @7
    @120
    cI
    @4
    @8
    @9
    @122
    oveqd
    eleq2d
    3anbi23d
    @120
    @65
    @20
    @72
    @29
    @120
    @61
    @16
    @64
    @19
    @120
    @59
    @14
    @60
    @15
    @120
    c.mi
    @13
    @0
    @1
    @120
    @13
    c.mi
    @105
    @96
    @107
    @110
    @113
    @115
    @117
    @119
    @95
    @96
    @97
    @100
    @104
    simpll2
    #
    ad6antr
    eqcomd
    #
    oveqd
    @120
    c.mi
    @13
    @8
    @7
    @124
    oveqd
    eqeq12d
    @120
    @62
    @17
    @63
    @18
    @120
    c.mi
    @13
    @1
    @3
    @124
    oveqd
    @120
    c.mi
    @13
    @7
    @9
    @124
    oveqd
    eqeq12d
    anbi12d
    @120
    @68
    @25
    @71
    @28
    @120
    @66
    @22
    @67
    @24
    @120
    c.mi
    @13
    @0
    @21
    @124
    oveqd
    @120
    c.mi
    @13
    @8
    @23
    @124
    oveqd
    eqeq12d
    @120
    @69
    @26
    @70
    @27
    @120
    c.mi
    @13
    @1
    @21
    @124
    oveqd
    @120
    c.mi
    @13
    @7
    @23
    @124
    oveqd
    eqeq12d
    anbi12d
    anbi12d
    anbi12d
    @120
    @75
    @32
    @76
    @33
    @120
    c.mi
    @13
    @3
    @21
    @124
    oveqd
    @120
    c.mi
    @13
    @9
    @23
    @124
    oveqd
    eqeq12d
    imbi12d
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    @98
    @92
    @50
    vx
    cP
    @36
    @99
    @101
    @91
    @49
    vy
    cP
    @36
    @103
    @105
    @90
    @48
    va
    cP
    @36
    @106
    @105
    @113
    wa
    #
    @89
    @47
    vb
    cP
    @36
    @105
    @102
    @113
    @106
    adantr
    #
    @125
    @115
    wa
    #
    @88
    @46
    vz
    cP
    @36
    @125
    @102
    @115
    @126
    adantr
    @127
    @107
    wa
    #
    @55
    @6
    @87
    @45
    @128
    @54
    @5
    @1
    @128
    cI
    @4
    @0
    @3
    @128
    @4
    cI
    @105
    @97
    @113
    @115
    @107
    @121
    ad3antrrr
    eqcomd
    oveqd
    eleq2d
    @128
    @62
    @17
    @60
    @15
    @128
    c.mi
    @13
    @1
    @3
    @128
    @13
    c.mi
    @105
    @96
    @113
    @115
    @107
    @123
    ad3antrrr
    eqcomd
    #
    oveqd
    @128
    c.mi
    @13
    @8
    @7
    @129
    oveqd
    eqeq12d
    anbi12d
    rexeqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    anbi12d
    sbcie3s
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
    vc
    vd
    df-trkgcb
    elab4g
end
