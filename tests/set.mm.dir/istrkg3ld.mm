include "wcel.mm"
include "c3.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "wf1.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "c2.mm"
include "wral.mm"
include "w3o.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "cpr.mm"
include "wne.mm"
include "cuz.mm"
include "wb.mm"
include "cz.mm"
include "cle.mm"
include "3z.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "2z.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "istrkgld.mm"
include "mpdan.mm"
include "fzo13pr.mm"
include "f1eq2.mm"
include "ax-mp.mm"
include "anbi1i.mm"
include "exbii.mm"
include "1z.mm"
include "1ne2.mm"
include "oveq1.mm"
include "eqidd.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "eqeq2d.mm"
include "csn.mm"
include "caddc.mm"
include "2p1e3.mm"
include "oveq2i.mm"
include "fzosn.mm"
include "eqtr3i.mm"
include "raleqi.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ralsng.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "f1prex.mm"
include "mp3an.mm"
include "3bitrd.mm"

theorem istrkg3ld
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
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
  let cN: class N
  assume istrkg.p: |- P = ( Base ` G )
  assume istrkg.d: |- .- = ( dist ` G )
  assume istrkg.i: |- I = ( Itv ` G )

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
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
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
  disjoint N f
  disjoint N g
  disjoint N j
  disjoint N n
  disjoint N p
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( G e. V -> ( G TarskiGDim>= 3 <-> E. u e. P E. v e. P ( u =/= v /\ E. x e. P E. y e. P E. z e. P ( ( ( u .- x ) = ( v .- x ) /\ ( u .- y ) = ( v .- y ) /\ ( u .- z ) = ( v .- z ) ) /\ -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) ) ) ) )

  proof
    cG
    cV
    wcel
    #
    cG
    c3
    cstrkgld
    wbr
    #
    c1
    c3
    cfzo
    co
    #
    cP
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
    c.mi
    co
    #
    vj
    cv
    #
    @3
    cfv
    #
    @6
    c.mi
    co
    #
    wceq
    #
    @5
    vy
    cv
    #
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
    vz
    cv
    #
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
    c2
    c3
    cfzo
    co
    #
    wral
    #
    @16
    @6
    @12
    cI
    co
    wcel
    @6
    @16
    @12
    cI
    co
    wcel
    @12
    @6
    @16
    cI
    co
    wcel
    w3o
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
    c2
    cpr
    #
    cP
    @3
    wf1
    #
    @27
    wa
    #
    vf
    wex
    #
    vu
    cv
    #
    vv
    cv
    #
    wne
    @34
    @6
    c.mi
    co
    #
    @35
    @6
    c.mi
    co
    #
    wceq
    #
    @34
    @12
    c.mi
    co
    #
    @35
    @12
    c.mi
    co
    #
    wceq
    #
    @34
    @16
    c.mi
    co
    #
    @35
    @16
    c.mi
    co
    #
    wceq
    #
    w3a
    #
    @23
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
    vv
    cP
    wrex
    vu
    cP
    wrex
    #
    @0
    c3
    c2
    cuz
    cfv
    wcel
    #
    @1
    @29
    wb
    @51
    @0
    @51
    c3
    cz
    wcel
    c2
    c3
    cle
    wbr
    3z
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    c2
    c3
    2z
    eluz1i
    mpbir2an
    a1i
    vx
    vy
    vz
    cP
    vf
    vj
    cG
    cI
    c.mi
    c3
    cV
    istrkg.p
    istrkg.d
    istrkg.i
    istrkgld
    mpdan
    @29
    @33
    wb
    @0
    @28
    @32
    vf
    @4
    @31
    @27
    @2
    @30
    wceq
    @4
    @31
    wb
    fzo13pr
    @2
    @30
    cP
    @3
    f1eq2
    ax-mp
    anbi1i
    exbii
    a1i
    @33
    @50
    wb
    #
    @0
    c1
    cz
    wcel
    c2
    cz
    wcel
    #
    c1
    c2
    wne
    @52
    1z
    2z
    1ne2
    @27
    @49
    @7
    @37
    wceq
    #
    @13
    @40
    wceq
    #
    @17
    @43
    wceq
    #
    w3a
    #
    @23
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
    vu
    vv
    c1
    c2
    cP
    vf
    cz
    cz
    @34
    @5
    wceq
    #
    @48
    @60
    vx
    cP
    @61
    @47
    @59
    vy
    cP
    @61
    @46
    @58
    vz
    cP
    @61
    @45
    @57
    @23
    @61
    @38
    @54
    @41
    @55
    @44
    @56
    @61
    @36
    @7
    @37
    @37
    @34
    @5
    @6
    c.mi
    oveq1
    @61
    @37
    eqidd
    eqeq12d
    @61
    @39
    @13
    @40
    @40
    @34
    @5
    @12
    c.mi
    oveq1
    @61
    @40
    eqidd
    eqeq12d
    @61
    @42
    @17
    @43
    @43
    @34
    @5
    @16
    c.mi
    oveq1
    @61
    @43
    eqidd
    eqeq12d
    3anbi123d
    anbi1d
    rexbidv
    rexbidv
    rexbidv
    @35
    c2
    @3
    cfv
    #
    wceq
    #
    @60
    @26
    vx
    cP
    @63
    @59
    @25
    vy
    cP
    @63
    @58
    @24
    vz
    cP
    @63
    @57
    @22
    @23
    @63
    @57
    @7
    @62
    @6
    c.mi
    co
    #
    wceq
    #
    @13
    @62
    @12
    c.mi
    co
    #
    wceq
    #
    @17
    @62
    @16
    c.mi
    co
    #
    wceq
    #
    w3a
    #
    @22
    @63
    @54
    @65
    @55
    @67
    @56
    @69
    @63
    @37
    @64
    @7
    @35
    @62
    @6
    c.mi
    oveq1
    eqeq2d
    @63
    @40
    @66
    @13
    @35
    @62
    @12
    c.mi
    oveq1
    eqeq2d
    @63
    @43
    @68
    @17
    @35
    @62
    @16
    c.mi
    oveq1
    eqeq2d
    3anbi123d
    @22
    @20
    vj
    c2
    csn
    #
    wral
    #
    @70
    @20
    vj
    @21
    @71
    c2
    c2
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @21
    @71
    @73
    c3
    c2
    cfzo
    2p1e3
    oveq2i
    @53
    @74
    @71
    wceq
    2z
    c2
    fzosn
    ax-mp
    eqtr3i
    raleqi
    @53
    @72
    @70
    wb
    2z
    @20
    @70
    vj
    c2
    cz
    @8
    c2
    wceq
    #
    @11
    @65
    @15
    @67
    @19
    @69
    @75
    @10
    @64
    @7
    @75
    @9
    @62
    @6
    c.mi
    @8
    c2
    @3
    fveq2
    #
    oveq1d
    eqeq2d
    @75
    @14
    @66
    @13
    @75
    @9
    @62
    @12
    c.mi
    @76
    oveq1d
    eqeq2d
    @75
    @18
    @68
    @17
    @75
    @9
    @62
    @16
    c.mi
    @76
    oveq1d
    eqeq2d
    3anbi123d
    ralsng
    ax-mp
    bitri
    syl6bbr
    anbi1d
    rexbidv
    rexbidv
    rexbidv
    f1prex
    mp3an
    a1i
    3bitrd
end
