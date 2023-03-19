include "wcel.mm"
include "c2.mm"
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
include "wral.mm"
include "w3o.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "cuz.mm"
include "wb.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "istrkgld.mm"
include "mpan2.mm"
include "r19.41v.mm"
include "ancom.mm"
include "rexbii.mm"
include "3bitr3ri.mm"
include "exbii.mm"
include "rexcom4.mm"
include "simpr.mm"
include "reximi.mm"
include "adantl.mm"
include "exlimiv.mm"
include "cmpt.mm"
include "csn.mm"
include "cop.mm"
include "wss.mm"
include "wf1o.mm"
include "1ex.mm"
include "vex.mm"
include "f1osn.mm"
include "f1of1.mm"
include "mp1i.mm"
include "snssi.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "wtru.mm"
include "fzo12sn.mm"
include "mpteq1.mm"
include "cvv.mm"
include "fmptsn.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "eqidd.mm"
include "f1eq123d.mm"
include "trud.mm"
include "sylibr.mm"
include "c0.mm"
include "ral0.mm"
include "fzo0.mm"
include "raleqi.mm"
include "mpbir.mm"
include "jctl.mm"
include "ovex.mm"
include "mptex.mm"
include "f1eq1.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "nfv.mm"
include "nfan.mm"
include "simpll.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "ralbida.mm"
include "anbi1d.mm"
include "2rexbidva.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2an.mm"
include "impbida.mm"
include "rexbiia.mm"
include "3bitr2i.mm"
include "syl6bb.mm"

theorem istrkg2ld
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let vu: setvar u
  let vv: setvar v
  let cN: class N
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
  disjoint N f
  disjoint N g
  disjoint N j
  disjoint N n
  disjoint N p
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( G e. V -> ( G TarskiGDim>= 2 <-> E. x e. P E. y e. P E. z e. P -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) ) )

  proof
    cG
    cV
    wcel
    #
    cG
    c2
    cstrkgld
    wbr
    #
    c1
    c2
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
    c2
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
    @23
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
    @0
    c2
    c2
    cuz
    cfv
    wcel
    #
    @1
    @29
    wb
    c2
    cz
    wcel
    @33
    2z
    c2
    uzid
    ax-mp
    vx
    vy
    vz
    cP
    vf
    vj
    cG
    cI
    c.mi
    c2
    cV
    istrkg.p
    istrkg.d
    istrkg.i
    istrkgld
    mpan2
    @29
    @4
    @26
    wa
    #
    vx
    cP
    wrex
    #
    vf
    wex
    @34
    vf
    wex
    #
    vx
    cP
    wrex
    @32
    @28
    @35
    vf
    @26
    @4
    wa
    #
    vx
    cP
    wrex
    @27
    @4
    wa
    @35
    @28
    @26
    @4
    vx
    cP
    r19.41v
    @37
    @34
    vx
    cP
    @26
    @4
    ancom
    rexbii
    @27
    @4
    ancom
    3bitr3ri
    exbii
    @34
    vx
    vf
    cP
    rexcom4
    @36
    @31
    vx
    cP
    @6
    cP
    wcel
    #
    @36
    @31
    @36
    @31
    @38
    @34
    @31
    vf
    @26
    @31
    @4
    @25
    @30
    vy
    cP
    @24
    @23
    vz
    cP
    @22
    @23
    simpr
    reximi
    reximi
    adantl
    exlimiv
    adantl
    @38
    @2
    cP
    vj
    @2
    @6
    cmpt
    #
    wf1
    #
    c1
    @39
    cfv
    #
    @6
    c.mi
    co
    #
    @8
    @39
    cfv
    #
    @6
    c.mi
    co
    #
    wceq
    #
    @41
    @12
    c.mi
    co
    #
    @43
    @12
    c.mi
    co
    #
    wceq
    #
    @41
    @16
    c.mi
    co
    #
    @43
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
    @36
    @31
    @38
    c1
    csn
    #
    cP
    c1
    @6
    cop
    csn
    #
    wf1
    #
    @40
    @38
    @57
    @6
    csn
    #
    @58
    wf1
    #
    @60
    cP
    wss
    @59
    @57
    @60
    @58
    wf1o
    @61
    @38
    c1
    @6
    1ex
    vx
    vex
    #
    f1osn
    @57
    @60
    @58
    f1of1
    mp1i
    @6
    cP
    snssi
    @57
    @60
    cP
    @58
    f1ss
    syl2anc
    @40
    @59
    wb
    wtru
    @2
    @57
    cP
    cP
    @39
    @58
    @39
    @58
    wceq
    wtru
    @39
    vj
    @57
    @6
    cmpt
    #
    @58
    @2
    @57
    wceq
    #
    @39
    @63
    wceq
    fzo12sn
    vj
    @2
    @57
    @6
    mpteq1
    ax-mp
    c1
    cvv
    wcel
    @6
    cvv
    wcel
    @58
    @63
    wceq
    1ex
    @62
    vj
    c1
    @6
    cvv
    cvv
    fmptsn
    mp2an
    eqtr4i
    a1i
    @64
    wtru
    fzo12sn
    a1i
    wtru
    cP
    eqidd
    f1eq123d
    trud
    sylibr
    @30
    @55
    vy
    cP
    @23
    @54
    vz
    cP
    @23
    @53
    @53
    @52
    vj
    c0
    wral
    @52
    vj
    ral0
    @52
    vj
    @21
    c0
    c2
    fzo0
    raleqi
    mpbir
    jctl
    reximi
    reximi
    @34
    @40
    @56
    wa
    vf
    @39
    vj
    @2
    @6
    c1
    c2
    cfzo
    ovex
    mptex
    @3
    @39
    wceq
    #
    @4
    @40
    @26
    @56
    @2
    cP
    @3
    @39
    f1eq1
    @65
    @24
    @54
    vy
    vz
    cP
    cP
    @65
    @12
    cP
    wcel
    @16
    cP
    wcel
    wa
    #
    wa
    #
    @22
    @53
    @23
    @67
    @20
    @52
    vj
    @21
    @65
    @66
    vj
    vj
    @3
    @39
    vj
    @2
    @6
    nfmpt1
    nfeq2
    @66
    vj
    nfv
    nfan
    @67
    @8
    @21
    wcel
    #
    wa
    #
    @11
    @45
    @15
    @48
    @19
    @51
    @69
    @7
    @42
    @10
    @44
    @69
    @5
    @41
    @6
    c.mi
    @69
    c1
    @3
    @39
    @65
    @66
    @68
    simpll
    #
    fveq1d
    #
    oveq1d
    @69
    @9
    @43
    @6
    c.mi
    @69
    @8
    @3
    @39
    @70
    fveq1d
    #
    oveq1d
    eqeq12d
    @69
    @13
    @46
    @14
    @47
    @69
    @5
    @41
    @12
    c.mi
    @71
    oveq1d
    @69
    @9
    @43
    @12
    c.mi
    @72
    oveq1d
    eqeq12d
    @69
    @17
    @49
    @18
    @50
    @69
    @5
    @41
    @16
    c.mi
    @71
    oveq1d
    @69
    @9
    @43
    @16
    c.mi
    @72
    oveq1d
    eqeq12d
    3anbi123d
    ralbida
    anbi1d
    2rexbidva
    anbi12d
    spcev
    syl2an
    impbida
    rexbiia
    3bitr2i
    syl6bb
end
