include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "simprl.mm"
include "simprr.mm"
include "dihord11c.mm"
include "syl123anc.mm"
include "wb.mm"
include "simpl11.mm"
include "simpl13.mm"
include "dicelval3.mm"
include "syl2anc.mm"
include "clat.mm"
include "simp11l.mm"
include "adantr.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "dibelval3.mm"
include "syl12anc.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpr.mm"
include "dihord10.mm"
include "3exp2.mm"
include "oveq12.mm"
include "eqeq2d.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "biimprd.mm"
include "com23.mm"
include "impr.mm"
include "com12.mm"
include "syl6.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "mpd.mm"
include "exp32.mm"
include "ralrimiv.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp2r.mm"
include "trlord.mm"
include "syl122anc.mm"
include "mpbird.mm"

theorem dihord2pre
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume dihjust.b: |- B = ( Base ` K )
  assume dihjust.l: |- .<_ = ( le ` K )
  assume dihjust.j: |- .\/ = ( join ` K )
  assume dihjust.m: |- ./\ = ( meet ` K )
  assume dihjust.a: |- A = ( Atoms ` K )
  assume dihjust.h: |- H = ( LHyp ` K )
  assume dihjust.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dihjust.J: |- J = ( ( DIsoC ` K ) ` W )
  assume dihjust.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjust.s: |- .(+) = ( LSSum ` U )
  assume dihord2c.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihord2c.r: |- R = ( ( trL ` K ) ` W )
  assume dihord2c.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dihord2.p: |- P = ( ( oc ` K ) ` W )
  assume dihord2.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihord2.d: |- .+ = ( +g ` U )
  assume dihord2.g: |- G = ( iota_ h e. T ( h ` P ) = N )

  disjoint A h
  disjoint P h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint .<_ h
  disjoint N h
  disjoint T h
  disjoint W h
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint f z
  disjoint .\/ f
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint .\/ g
  disjoint s y
  disjoint s z
  disjoint .\/ s
  disjoint y z
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ f
  disjoint ./\ g
  disjoint ./\ s
  disjoint ./\ y
  disjoint ./\ z
  disjoint .(+) f
  disjoint .(+) g
  disjoint .(+) s
  disjoint .(+) y
  disjoint .(+) z
  disjoint E g
  disjoint E s
  disjoint .+ g
  disjoint .+ s
  disjoint .+ y
  disjoint .+ z
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint h s
  disjoint h y
  disjoint h z
  disjoint A s
  disjoint A y
  disjoint A z
  disjoint I f
  disjoint I g
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint J f
  disjoint J g
  disjoint J s
  disjoint J y
  disjoint J z
  disjoint G g
  disjoint O g
  disjoint O s
  disjoint O y
  disjoint O z
  disjoint Q f
  disjoint Q g
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint R f
  disjoint R g
  disjoint R s
  disjoint R y
  disjoint R z
  disjoint B f
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint H f
  disjoint H g
  disjoint H s
  disjoint H y
  disjoint H z
  disjoint K f
  disjoint K g
  disjoint K s
  disjoint K y
  disjoint K z
  disjoint U y
  disjoint U z
  disjoint .<_ f
  disjoint .<_ g
  disjoint .<_ s
  disjoint .<_ y
  disjoint .<_ z
  disjoint N f
  disjoint N g
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint T f
  disjoint T g
  disjoint T s
  disjoint T y
  disjoint T z
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint W y
  disjoint W z
  disjoint X f
  disjoint X g
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y s
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` N ) .(+) ( I ` ( Y ./\ W ) ) ) ) -> ( X ./\ W ) .<_ ( Y ./\ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cN
    cA
    wcel
    cN
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cQ
    cJ
    cfv
    cX
    cW
    c.an
    co
    #
    cI
    cfv
    c.po
    co
    cN
    cJ
    cfv
    #
    cY
    cW
    c.an
    co
    #
    cI
    cfv
    #
    c.po
    co
    wss
    #
    w3a
    #
    @9
    @11
    c.le
    wbr
    #
    vf
    cv
    #
    cR
    cfv
    #
    @9
    c.le
    wbr
    #
    @17
    @11
    c.le
    wbr
    #
    wi
    #
    vf
    cT
    wral
    #
    @14
    @20
    vf
    cT
    @14
    @16
    cT
    wcel
    #
    @18
    @19
    @14
    @22
    @18
    wa
    #
    wa
    #
    @16
    cO
    cop
    #
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vz
    @12
    wrex
    vy
    @10
    wrex
    #
    @19
    @24
    @5
    @6
    @7
    @13
    @22
    @18
    @30
    @5
    @8
    @13
    @23
    simpl1
    @6
    @7
    @5
    @13
    @23
    simpl2l
    @6
    @7
    @5
    @13
    @23
    simpl2r
    #
    @5
    @8
    @13
    @23
    simpl3
    @14
    @22
    @18
    simprl
    @14
    @22
    @18
    simprr
    vy
    vz
    cA
    cB
    cP
    c.pl
    c.po
    cQ
    cR
    cT
    cU
    vf
    vh
    cE
    cG
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cY
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.m
    dihjust.a
    dihjust.h
    dihjust.i
    dihjust.J
    dihjust.u
    dihjust.s
    dihord2c.t
    dihord2c.r
    dihord2c.o
    dihord2.p
    dihord2.e
    dihord2.d
    dihord2.g
    dihord11c
    syl123anc
    @24
    @29
    @19
    vy
    vz
    @10
    @12
    @24
    @26
    @10
    wcel
    #
    @27
    @12
    wcel
    #
    wa
    @26
    cG
    vs
    cv
    #
    cfv
    @34
    cop
    #
    wceq
    #
    vs
    cE
    wrex
    #
    @27
    vg
    cv
    #
    cO
    cop
    #
    wceq
    #
    @38
    cR
    cfv
    @11
    c.le
    wbr
    #
    wa
    #
    vg
    cT
    wrex
    #
    wa
    #
    @29
    @19
    wi
    #
    @24
    @32
    @37
    @33
    @43
    @24
    @2
    @4
    @32
    @37
    wb
    @2
    @3
    @4
    @8
    @13
    @23
    simpl11
    #
    @2
    @3
    @4
    @8
    @13
    @23
    simpl13
    cA
    cP
    cN
    cT
    vh
    cE
    cG
    cH
    cJ
    cK
    c.le
    chlt
    cW
    @26
    vs
    dihjust.l
    dihjust.a
    dihjust.h
    dihord2.p
    dihord2c.t
    dihord2.e
    dihjust.J
    dihord2.g
    dicelval3
    syl2anc
    @24
    @2
    @11
    cB
    wcel
    #
    @11
    cW
    c.le
    wbr
    #
    @33
    @43
    wb
    @46
    @24
    cK
    clat
    wcel
    #
    @7
    cW
    cB
    wcel
    #
    @47
    @24
    @0
    @49
    @14
    @0
    @23
    @0
    @1
    @3
    @4
    @8
    @13
    simp11l
    #
    adantr
    cK
    hllat
    #
    syl
    #
    @31
    @24
    @1
    @50
    @14
    @1
    @23
    @0
    @1
    @3
    @4
    @8
    @13
    simp11r
    #
    adantr
    cB
    cH
    cK
    cW
    dihjust.b
    dihjust.h
    lhpbase
    #
    syl
    #
    cB
    cK
    c.an
    cY
    cW
    dihjust.b
    dihjust.m
    latmcl
    #
    syl3anc
    @24
    @49
    @7
    @50
    @48
    @53
    @31
    @56
    cB
    cK
    c.le
    c.an
    cY
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    #
    syl3anc
    cB
    cR
    cT
    vg
    vh
    cH
    cI
    cK
    c.le
    chlt
    cW
    @11
    @27
    cO
    dihjust.b
    dihjust.l
    dihjust.h
    dihord2c.t
    dihord2c.r
    dihord2c.o
    dihjust.i
    dibelval3
    syl12anc
    anbi12d
    @44
    @36
    @42
    wa
    #
    vg
    cT
    wrex
    vs
    cE
    wrex
    @24
    @45
    @36
    @42
    vs
    vg
    cE
    cT
    reeanv
    @24
    @59
    @45
    vs
    vg
    cE
    cT
    @24
    @34
    cE
    wcel
    @38
    cT
    wcel
    wa
    #
    @41
    @25
    @35
    @39
    c.pl
    co
    #
    wceq
    #
    @19
    wi
    #
    wi
    #
    @59
    @45
    wi
    @24
    @60
    @41
    @62
    @19
    @24
    @60
    @41
    @62
    w3a
    #
    wa
    @5
    @23
    @65
    @19
    @5
    @8
    @13
    @23
    @65
    simpll1
    @14
    @23
    @65
    simplr
    @24
    @65
    simpr
    cA
    cB
    cP
    c.pl
    c.po
    cQ
    cR
    cT
    cU
    vf
    vg
    vh
    cE
    cG
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cY
    vs
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.m
    dihjust.a
    dihjust.h
    dihjust.i
    dihjust.J
    dihjust.u
    dihjust.s
    dihord2c.t
    dihord2c.r
    dihord2c.o
    dihord2.p
    dihord2.e
    dihord2.d
    dihord2.g
    dihord10
    syl3anc
    3exp2
    @59
    @64
    @45
    @36
    @40
    @41
    @64
    @45
    wi
    @36
    @40
    wa
    #
    @64
    @41
    @45
    @66
    @41
    @45
    wi
    @64
    @66
    @45
    @63
    @41
    @66
    @29
    @62
    @19
    @66
    @28
    @61
    @25
    @26
    @35
    @27
    @39
    c.pl
    oveq12
    eqeq2d
    imbi1d
    imbi2d
    biimprd
    com23
    impr
    com12
    syl6
    rexlimdvv
    syl5bir
    sylbid
    rexlimdvv
    mpd
    exp32
    ralrimiv
    @14
    @2
    @9
    cB
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    @47
    @48
    @15
    @21
    wb
    @2
    @3
    @4
    @8
    @13
    simp11
    @14
    @49
    @6
    @50
    @67
    @14
    @0
    @49
    @51
    @52
    syl
    #
    @5
    @6
    @7
    @13
    simp2l
    #
    @14
    @1
    @50
    @54
    @55
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    @14
    @49
    @6
    @50
    @68
    @69
    @70
    @71
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
    @14
    @49
    @7
    @50
    @47
    @69
    @5
    @6
    @7
    @13
    simp2r
    #
    @71
    @57
    syl3anc
    @14
    @49
    @7
    @50
    @48
    @69
    @72
    @71
    @58
    syl3anc
    cA
    cB
    cR
    cT
    vf
    cH
    cK
    c.le
    cW
    @9
    @11
    dihjust.b
    dihjust.l
    dihjust.a
    dihjust.h
    dihord2c.t
    dihord2c.r
    trlord
    syl122anc
    mpbird
end
