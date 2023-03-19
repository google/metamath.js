include "c1.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wf1.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "c2.mm"
include "wral.mm"
include "wcel.mm"
include "w3o.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "citv.mm"
include "wsbc.mm"
include "cds.mm"
include "cbs.mm"
include "cuz.mm"
include "cstrkgld.mm"
include "eqidd.mm"
include "simp1.mm"
include "eqcomd.mm"
include "f1eq123d.mm"
include "simp2.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "ralbidv.mm"
include "simp3.mm"
include "eleq2d.mm"
include "3orbi123d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "exbidv.mm"
include "sbcie3s.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "df-trkgld.mm"
include "brabg.mm"

theorem istrkgld
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let vf: setvar f
  let vj: setvar j
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let vd: setvar d
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume istrkg.p: |- P = ( Base ` G )
  assume istrkg.d: |- .- = ( dist ` G )
  assume istrkg.i: |- I = ( Itv ` G )

  disjoint G f
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint I f
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P f
  disjoint P j
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- f
  disjoint .- j
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint N f
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint N z
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
  disjoint P g
  disjoint P i
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
  disjoint .- g
  disjoint .- i
  disjoint .- n
  disjoint .- p
  disjoint .- u
  disjoint .- v
  disjoint N g
  disjoint N n
  disjoint N p
  assert |- ( ( G e. V /\ N e. ( ZZ>= ` 2 ) ) -> ( G TarskiGDim>= N <-> E. f ( f : ( 1 ..^ N ) -1-1-> P /\ E. x e. P E. y e. P E. z e. P ( A. j e. ( 2 ..^ N ) ( ( ( f ` 1 ) .- x ) = ( ( f ` j ) .- x ) /\ ( ( f ` 1 ) .- y ) = ( ( f ` j ) .- y ) /\ ( ( f ` 1 ) .- z ) = ( ( f ` j ) .- z ) ) /\ -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) ) ) ) )

  proof
    c1
    vn
    cv
    #
    cfzo
    co
    #
    vp
    cv
    #
    vf
    cv
    #
    wf1
    #
    c1
    @3
    cfv
    #
    vx
    cv
    #
    vd
    cv
    #
    co
    #
    vj
    cv
    @3
    cfv
    #
    @6
    @7
    co
    #
    wceq
    #
    @5
    vy
    cv
    #
    @7
    co
    #
    @9
    @12
    @7
    co
    #
    wceq
    #
    @5
    vz
    cv
    #
    @7
    co
    #
    @9
    @16
    @7
    co
    #
    wceq
    #
    w3a
    #
    vj
    c2
    @0
    cfzo
    co
    #
    wral
    #
    @16
    @6
    @12
    vi
    cv
    #
    co
    #
    wcel
    #
    @6
    @16
    @12
    @23
    co
    #
    wcel
    #
    @12
    @6
    @16
    @23
    co
    #
    wcel
    #
    w3o
    #
    wn
    #
    wa
    #
    vz
    @2
    wrex
    #
    vy
    @2
    wrex
    #
    vx
    @2
    wrex
    #
    wa
    #
    vf
    wex
    #
    vi
    vg
    cv
    #
    citv
    cfv
    wsbc
    vd
    @38
    cds
    cfv
    wsbc
    vp
    @38
    cbs
    cfv
    wsbc
    @1
    cP
    @3
    wf1
    #
    @5
    @6
    c.mi
    co
    #
    @9
    @6
    c.mi
    co
    #
    wceq
    #
    @5
    @12
    c.mi
    co
    #
    @9
    @12
    c.mi
    co
    #
    wceq
    #
    @5
    @16
    c.mi
    co
    #
    @9
    @16
    c.mi
    co
    #
    wceq
    #
    w3a
    #
    vj
    @21
    wral
    #
    @16
    @6
    @12
    cI
    co
    #
    wcel
    #
    @6
    @16
    @12
    cI
    co
    #
    wcel
    #
    @12
    @6
    @16
    cI
    co
    #
    wcel
    #
    w3o
    #
    wn
    #
    wa
    #
    vz
    cP
    wrex
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    wa
    #
    vf
    wex
    #
    c1
    cN
    cfzo
    co
    #
    cP
    @3
    wf1
    #
    @49
    vj
    c2
    cN
    cfzo
    co
    #
    wral
    #
    @58
    wa
    #
    vz
    cP
    wrex
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    wa
    #
    vf
    wex
    vg
    vn
    cG
    cN
    cV
    c2
    cuz
    cfv
    cstrkgld
    @64
    @37
    vg
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
    @2
    cP
    wceq
    #
    @7
    c.mi
    wceq
    #
    @23
    cI
    wceq
    #
    w3a
    #
    @63
    @36
    vf
    @76
    @39
    @4
    @62
    @35
    @76
    @1
    @1
    cP
    @2
    @3
    @3
    @76
    @3
    eqidd
    @76
    @1
    eqidd
    @76
    @2
    cP
    @73
    @74
    @75
    simp1
    eqcomd
    #
    f1eq123d
    @76
    @61
    @34
    vx
    cP
    @2
    @77
    @76
    @60
    @33
    vy
    cP
    @2
    @77
    @76
    @59
    @32
    vz
    cP
    @2
    @77
    @76
    @50
    @22
    @58
    @31
    @76
    @49
    @20
    vj
    @21
    @76
    @42
    @11
    @45
    @15
    @48
    @19
    @76
    @40
    @8
    @41
    @10
    @76
    c.mi
    @7
    @5
    @6
    @76
    @7
    c.mi
    @73
    @74
    @75
    simp2
    eqcomd
    #
    oveqd
    @76
    c.mi
    @7
    @9
    @6
    @78
    oveqd
    eqeq12d
    @76
    @43
    @13
    @44
    @14
    @76
    c.mi
    @7
    @5
    @12
    @78
    oveqd
    @76
    c.mi
    @7
    @9
    @12
    @78
    oveqd
    eqeq12d
    @76
    @46
    @17
    @47
    @18
    @76
    c.mi
    @7
    @5
    @16
    @78
    oveqd
    @76
    c.mi
    @7
    @9
    @16
    @78
    oveqd
    eqeq12d
    3anbi123d
    ralbidv
    @76
    @57
    @30
    @76
    @52
    @25
    @54
    @27
    @56
    @29
    @76
    @51
    @24
    @16
    @76
    cI
    @23
    @6
    @12
    @76
    @23
    cI
    @73
    @74
    @75
    simp3
    eqcomd
    #
    oveqd
    eleq2d
    @76
    @53
    @26
    @6
    @76
    cI
    @23
    @16
    @12
    @79
    oveqd
    eleq2d
    @76
    @55
    @28
    @12
    @76
    cI
    @23
    @6
    @16
    @79
    oveqd
    eleq2d
    3orbi123d
    notbid
    anbi12d
    rexeqbidv
    rexeqbidv
    rexeqbidv
    anbi12d
    exbidv
    sbcie3s
    @0
    cN
    wceq
    #
    @63
    @72
    vf
    @80
    @39
    @66
    @62
    @71
    @80
    @1
    @65
    cP
    cP
    @3
    @3
    @80
    @3
    eqidd
    @0
    cN
    c1
    cfzo
    oveq2
    @80
    cP
    eqidd
    f1eq123d
    @80
    @60
    @70
    vx
    vy
    cP
    cP
    @80
    @59
    @69
    vz
    cP
    @80
    @50
    @68
    @58
    @80
    @49
    vj
    @21
    @67
    @0
    cN
    c2
    cfzo
    oveq2
    raleqdv
    anbi1d
    rexbidv
    2rexbidv
    anbi12d
    exbidv
    vx
    vy
    vz
    vf
    vg
    vi
    vj
    vn
    vp
    vd
    df-trkgld
    brabg
end
