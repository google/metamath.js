include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cpw.mm"
include "w3a.mm"
include "citv.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cstrkgb.mm"
include "simpl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "simpllr.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "imbi1d.mm"
include "raleqbidva.mm"
include "simp-6r.mm"
include "anbi12d.mm"
include "oveqdr.mm"
include "rexeqbidva.mm"
include "imbi12d.mm"
include "pweqd.mm"
include "ad2antrr.mm"
include "simp-4r.mm"
include "2ralbidv.mm"
include "3anbi123d.mm"
include "sbcie2s.mm"
include "df-trkgb.mm"
include "elab4g.mm"

theorem istrkgb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vs: setvar s
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
  assume istrkg.p: |- P = ( Base ` G )
  assume istrkg.d: |- .- = ( dist ` G )
  assume istrkg.i: |- I = ( Itv ` G )

  disjoint a b
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint I b
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
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P a
  disjoint P b
  disjoint P s
  disjoint P t
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
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b n
  disjoint b p
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
  disjoint P c
  disjoint P d
  disjoint P f
  disjoint P g
  disjoint P i
  disjoint P j
  disjoint P n
  disjoint P p
  disjoint .- c
  disjoint .- d
  disjoint .- f
  disjoint .- g
  disjoint .- i
  disjoint .- j
  disjoint .- n
  disjoint .- p
  assert |- ( G e. TarskiGB <-> ( G e. _V /\ ( A. x e. P A. y e. P ( y e. ( x I x ) -> x = y ) /\ A. x e. P A. y e. P A. z e. P A. u e. P A. v e. P ( ( u e. ( x I z ) /\ v e. ( y I z ) ) -> E. a e. P ( a e. ( u I y ) /\ a e. ( v I x ) ) ) /\ A. s e. ~P P A. t e. ~P P ( E. a e. P A. x e. s A. y e. t x e. ( a I y ) -> E. b e. P A. x e. s A. y e. t b e. ( x I y ) ) ) ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    @1
    vi
    cv
    #
    co
    #
    wcel
    #
    @1
    @0
    wceq
    #
    wi
    #
    vy
    vp
    cv
    #
    wral
    #
    vx
    @7
    wral
    #
    vu
    cv
    #
    @1
    vz
    cv
    #
    @2
    co
    #
    wcel
    #
    vv
    cv
    #
    @0
    @11
    @2
    co
    #
    wcel
    #
    wa
    #
    va
    cv
    #
    @10
    @0
    @2
    co
    #
    wcel
    #
    @18
    @14
    @1
    @2
    co
    #
    wcel
    #
    wa
    #
    va
    @7
    wrex
    #
    wi
    #
    vv
    @7
    wral
    #
    vu
    @7
    wral
    #
    vz
    @7
    wral
    #
    vy
    @7
    wral
    #
    vx
    @7
    wral
    #
    @1
    @18
    @0
    @2
    co
    #
    wcel
    #
    vy
    vt
    cv
    #
    wral
    vx
    vs
    cv
    #
    wral
    #
    va
    @7
    wrex
    #
    vb
    cv
    #
    @1
    @0
    @2
    co
    #
    wcel
    #
    vy
    @33
    wral
    vx
    @34
    wral
    #
    vb
    @7
    wrex
    #
    wi
    #
    vt
    @7
    cpw
    #
    wral
    #
    vs
    @43
    wral
    #
    w3a
    #
    vi
    vf
    cv
    #
    citv
    cfv
    wsbc
    vp
    @47
    cbs
    cfv
    wsbc
    @0
    @1
    @1
    cI
    co
    #
    wcel
    #
    @5
    wi
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    @10
    @1
    @11
    cI
    co
    #
    wcel
    #
    @14
    @0
    @11
    cI
    co
    #
    wcel
    #
    wa
    #
    @18
    @10
    @0
    cI
    co
    #
    wcel
    #
    @18
    @14
    @1
    cI
    co
    #
    wcel
    #
    wa
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
    @1
    @18
    @0
    cI
    co
    #
    wcel
    #
    vy
    @33
    wral
    vx
    @34
    wral
    #
    va
    cP
    wrex
    #
    @37
    @1
    @0
    cI
    co
    #
    wcel
    #
    vy
    @33
    wral
    vx
    @34
    wral
    #
    vb
    cP
    wrex
    #
    wi
    #
    vt
    cP
    cpw
    #
    wral
    #
    vs
    @79
    wral
    #
    w3a
    #
    vf
    cG
    cstrkgb
    @82
    @46
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
    @7
    cP
    wceq
    #
    @2
    cI
    wceq
    #
    wa
    #
    @52
    @9
    @69
    @30
    @81
    @45
    @85
    @51
    @8
    vx
    cP
    @7
    @85
    @7
    cP
    @83
    @84
    simpl
    eqcomd
    #
    @85
    @1
    cP
    wcel
    #
    wa
    #
    @50
    @6
    vy
    cP
    @7
    @85
    cP
    @7
    wceq
    #
    @87
    @86
    adantr
    #
    @88
    @0
    cP
    wcel
    #
    wa
    #
    @49
    @4
    @5
    @92
    @48
    @3
    @0
    @92
    cI
    @2
    @1
    @1
    @92
    @2
    cI
    @83
    @84
    @87
    @91
    simpllr
    eqcomd
    oveqd
    eleq2d
    imbi1d
    raleqbidva
    raleqbidva
    @85
    @68
    @29
    vx
    cP
    @7
    @86
    @88
    @67
    @28
    vy
    cP
    @7
    @90
    @92
    @66
    @27
    vz
    cP
    @7
    @88
    @89
    @91
    @90
    adantr
    #
    @92
    @11
    cP
    wcel
    #
    wa
    #
    @65
    @26
    vu
    cP
    @7
    @92
    @89
    @94
    @93
    adantr
    #
    @95
    @10
    cP
    wcel
    #
    wa
    #
    @64
    @25
    vv
    cP
    @7
    @95
    @89
    @97
    @96
    adantr
    #
    @98
    @14
    cP
    wcel
    #
    wa
    #
    @57
    @17
    @63
    @24
    @101
    @54
    @13
    @56
    @16
    @101
    @53
    @12
    @10
    @101
    cI
    @2
    @1
    @11
    @101
    @2
    cI
    @83
    @84
    @87
    @91
    @94
    @97
    @100
    simp-6r
    eqcomd
    #
    oveqd
    eleq2d
    @101
    @55
    @15
    @14
    @101
    cI
    @2
    @0
    @11
    @102
    oveqd
    eleq2d
    anbi12d
    @101
    @62
    @23
    va
    cP
    @7
    @98
    @89
    @100
    @99
    adantr
    @101
    @18
    cP
    wcel
    #
    wa
    #
    @59
    @20
    @61
    @22
    @104
    @58
    @19
    @18
    @101
    @103
    vu
    vy
    cI
    @2
    @102
    oveqdr
    eleq2d
    @104
    @60
    @21
    @18
    @101
    @103
    vv
    vx
    cI
    @2
    @102
    oveqdr
    eleq2d
    anbi12d
    rexeqbidva
    imbi12d
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    raleqbidva
    @85
    @80
    @44
    vs
    @79
    @43
    @85
    cP
    @7
    @86
    pweqd
    #
    @85
    @34
    @79
    wcel
    #
    wa
    #
    @78
    @42
    vt
    @79
    @43
    @85
    @79
    @43
    wceq
    @106
    @105
    adantr
    @107
    @33
    @79
    wcel
    #
    wa
    #
    @73
    @36
    @77
    @41
    @109
    @72
    @35
    va
    cP
    @7
    @85
    @89
    @106
    @108
    @86
    ad2antrr
    #
    @109
    @103
    wa
    #
    @71
    @32
    vx
    vy
    @34
    @33
    @111
    @70
    @31
    @1
    @111
    cI
    @2
    @18
    @0
    @111
    @2
    cI
    @83
    @84
    @106
    @108
    @103
    simp-4r
    eqcomd
    oveqd
    eleq2d
    2ralbidv
    rexeqbidva
    @109
    @76
    @40
    vb
    cP
    @7
    @110
    @109
    @37
    cP
    wcel
    #
    wa
    #
    @75
    @39
    vx
    vy
    @34
    @33
    @113
    @74
    @38
    @37
    @113
    cI
    @2
    @1
    @0
    @113
    @2
    cI
    @83
    @84
    @106
    @108
    @112
    simp-4r
    eqcomd
    oveqd
    eleq2d
    2ralbidv
    rexeqbidva
    imbi12d
    raleqbidva
    raleqbidva
    3anbi123d
    sbcie2s
    vx
    vy
    vz
    vv
    vu
    vt
    vf
    vi
    vs
    vp
    va
    vb
    df-trkgb
    elab4g
end
