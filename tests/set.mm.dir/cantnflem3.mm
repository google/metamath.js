include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "crn.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "wcel.mm"
include "wceq.mm"
include "wss.mm"
include "con0.mm"
include "c0.mm"
include "c1o.mm"
include "cdif.mm"
include "w3a.mm"
include "c2o.mm"
include "wa.mm"
include "cantnflem2.mm"
include "eqid.mm"
include "3pm3.2i.mm"
include "oeeui.mm"
include "mpbiri.mm"
include "syl.mm"
include "simpld.mm"
include "simp1d.mm"
include "oecl.mm"
include "syl2anc.mm"
include "simp2d.mm"
include "eldifad.mm"
include "onelon.mm"
include "wne.mm"
include "dif1o.mm"
include "simprbi.mm"
include "wb.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "omword1.mm"
include "syl21anc.mm"
include "omcl.mm"
include "simp3d.mm"
include "oaword1.mm"
include "simprd.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "wi.mm"
include "ontr2.mm"
include "mp2and.mm"
include "oeord.mm"
include "syl3anc.mm"
include "csupp.mm"
include "cv.mm"
include "adantr.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "wfn.mm"
include "cvv.mm"
include "ffn.mm"
include "0ex.mm"
include "a1i.mm"
include "elsuppfn.mm"
include "simplbda.mm"
include "cep.mm"
include "coi.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "cantnfle.mm"
include "ex.mm"
include "ssrdv.mm"
include "cantnfp1.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cantnff.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"

theorem cantnflem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let cD: class D
  let cM: class M
  let cH: class H
  let cK: class K
  let cO: class O
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume oemapval.t: |- T = { <. x , y >. | E. z e. B ( ( x ` z ) e. ( y ` z ) /\ A. w e. B ( z e. w -> ( x ` w ) = ( y ` w ) ) ) }
  assume cantnf.c: |- ( ph -> C e. ( A ^o B ) )
  assume cantnf.s: |- ( ph -> C C_ ran ( A CNF B ) )
  assume cantnf.e: |- ( ph -> (/) e. C )
  assume cantnf.x: |- X = U. |^| { c e. On | C e. ( A ^o c ) }
  assume cantnf.p: |- P = ( iota d E. a e. On E. b e. ( A ^o X ) ( d = <. a , b >. /\ ( ( ( A ^o X ) .o a ) +o b ) = C ) )
  assume cantnf.y: |- Y = ( 1st ` P )
  assume cantnf.z: |- Z = ( 2nd ` P )
  assume cantnf.g: |- ( ph -> G e. S )
  assume cantnf.v: |- ( ph -> ( ( A CNF B ) ` G ) = Z )
  assume cantnf.f: |- F = ( t e. B |-> if ( t = X , Y , ( G ` t ) ) )

  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b c
  disjoint b d
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint c d
  disjoint C c
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint C d
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a t
  disjoint A a
  disjoint b t
  disjoint A b
  disjoint A c
  disjoint d t
  disjoint A d
  disjoint A t
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint T c
  disjoint T t
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G t
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X t
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h k
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint a g
  disjoint b g
  disjoint d g
  disjoint C g
  disjoint D k
  disjoint D n
  disjoint D z
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint b f
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b u
  disjoint b v
  disjoint d f
  disjoint d h
  disjoint d k
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A k
  disjoint A n
  disjoint A u
  disjoint A v
  disjoint M x
  disjoint M y
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S u
  disjoint S v
  disjoint Z g
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint O k
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint Y k
  disjoint X k
  disjoint X u
  assert |- ( ph -> C e. ran ( A CNF B ) )

  proof
    wph
    cF
    cA
    cB
    ccnf
    co
    #
    cfv
    #
    cC
    @0
    crn
    #
    wph
    @1
    cA
    cX
    coe
    co
    #
    cY
    comu
    co
    #
    cG
    @0
    cfv
    #
    coa
    co
    #
    @4
    cZ
    coa
    co
    #
    cC
    wph
    cF
    cS
    wcel
    #
    @1
    @6
    wceq
    #
    wph
    vt
    cA
    cB
    cS
    cF
    cG
    cX
    cY
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnf.g
    wph
    cX
    cB
    wcel
    #
    @3
    cA
    cB
    coe
    co
    #
    wcel
    #
    wph
    @3
    cC
    wss
    #
    cC
    @11
    wcel
    #
    @12
    wph
    @3
    @4
    cC
    wph
    @3
    con0
    wcel
    #
    cY
    con0
    wcel
    #
    c0
    cY
    wcel
    #
    @3
    @4
    wss
    wph
    cA
    con0
    wcel
    #
    cX
    con0
    wcel
    #
    @15
    cantnfs.a
    wph
    @19
    cY
    cA
    c1o
    cdif
    wcel
    #
    cZ
    @3
    wcel
    #
    wph
    @19
    @20
    @21
    w3a
    #
    @7
    cC
    wceq
    #
    wph
    cA
    con0
    c2o
    cdif
    wcel
    #
    cC
    con0
    c1o
    cdif
    wcel
    #
    wa
    #
    @22
    @23
    wa
    #
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cS
    cT
    cantnfs.s
    cantnfs.a
    cantnfs.b
    oemapval.t
    cantnf.c
    cantnf.s
    cantnf.e
    cantnflem2
    #
    @26
    @27
    cX
    cX
    wceq
    #
    cY
    cY
    wceq
    #
    cZ
    cZ
    wceq
    #
    w3a
    @29
    @30
    @31
    cX
    eqid
    cY
    eqid
    cZ
    eqid
    3pm3.2i
    vc
    va
    vb
    vd
    cA
    cC
    cX
    cY
    cP
    cZ
    cX
    cY
    cZ
    cantnf.x
    cantnf.p
    cantnf.y
    cantnf.z
    oeeui
    mpbiri
    syl
    #
    simpld
    #
    simp1d
    #
    cA
    cX
    oecl
    syl2anc
    #
    wph
    @18
    cY
    cA
    wcel
    #
    @16
    cantnfs.a
    wph
    cY
    cA
    c1o
    wph
    @19
    @20
    @21
    @33
    simp2d
    #
    eldifad
    #
    cA
    cY
    onelon
    syl2anc
    #
    wph
    @17
    cY
    c0
    wne
    #
    wph
    @20
    @40
    @37
    @20
    @36
    @40
    cY
    cA
    dif1o
    simprbi
    syl
    wph
    @16
    @17
    @40
    wb
    @39
    cY
    on0eln0
    syl
    mpbird
    @3
    cY
    omword1
    syl21anc
    wph
    @4
    @7
    cC
    wph
    @4
    con0
    wcel
    #
    cZ
    con0
    wcel
    #
    @4
    @7
    wss
    wph
    @15
    @16
    @41
    @35
    @39
    @3
    cY
    omcl
    syl2anc
    wph
    @15
    @21
    @42
    @35
    wph
    @19
    @20
    @21
    @33
    simp3d
    #
    @3
    cZ
    onelon
    syl2anc
    @4
    cZ
    oaword1
    syl2anc
    wph
    @22
    @23
    @32
    simprd
    #
    sseqtrd
    sstrd
    cantnf.c
    wph
    @15
    @11
    con0
    wcel
    #
    @13
    @14
    wa
    @12
    wi
    @35
    wph
    @18
    cB
    con0
    wcel
    #
    @45
    cantnfs.a
    cantnfs.b
    cA
    cB
    oecl
    syl2anc
    @3
    cC
    @11
    ontr2
    syl2anc
    mp2and
    wph
    @19
    @46
    @24
    @10
    @12
    wb
    @34
    cantnfs.b
    wph
    @24
    @25
    @28
    simpld
    #
    cX
    cB
    cA
    oeord
    syl3anc
    mpbird
    @38
    wph
    vx
    cG
    c0
    csupp
    co
    #
    cX
    wph
    vx
    cv
    #
    @48
    wcel
    #
    @49
    cX
    wcel
    #
    wph
    @50
    wa
    #
    @51
    cA
    @49
    coe
    co
    #
    @3
    wcel
    #
    @52
    @53
    cZ
    wss
    #
    @21
    @54
    @52
    @53
    @53
    @49
    cG
    cfv
    #
    comu
    co
    #
    cZ
    @52
    @53
    con0
    wcel
    #
    @56
    con0
    wcel
    #
    c0
    @56
    wcel
    #
    @53
    @57
    wss
    @52
    @18
    @49
    con0
    wcel
    #
    @58
    wph
    @18
    @50
    cantnfs.a
    adantr
    #
    @52
    @46
    @49
    cB
    wcel
    #
    @61
    wph
    @46
    @50
    cantnfs.b
    adantr
    #
    wph
    @48
    cB
    @49
    wph
    cG
    cdm
    #
    @48
    cB
    cG
    c0
    suppssdm
    wph
    cB
    cA
    cG
    wf
    #
    @65
    cB
    wceq
    wph
    @66
    cG
    c0
    cfsupp
    wbr
    #
    wph
    cG
    cS
    wcel
    #
    @66
    @67
    wa
    cantnf.g
    wph
    cA
    cB
    cS
    cG
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbid
    simpld
    #
    cB
    cA
    cG
    fdm
    syl
    syl5sseq
    sselda
    #
    cB
    @49
    onelon
    syl2anc
    #
    cA
    @49
    oecl
    syl2anc
    #
    @52
    @18
    @56
    cA
    wcel
    @59
    @62
    @52
    cB
    cA
    @49
    cG
    wph
    @66
    @50
    @69
    adantr
    @70
    ffvelrnd
    cA
    @56
    onelon
    syl2anc
    #
    @52
    @60
    @56
    c0
    wne
    #
    wph
    @50
    @63
    @74
    wph
    cG
    cB
    wfn
    #
    @46
    c0
    cvv
    wcel
    #
    @50
    @63
    @74
    wa
    wb
    wph
    @66
    @75
    @69
    cB
    cA
    cG
    ffn
    syl
    cantnfs.b
    @76
    wph
    0ex
    a1i
    @49
    cG
    con0
    cvv
    cB
    c0
    elsuppfn
    syl3anc
    simplbda
    @52
    @59
    @60
    @74
    wb
    @73
    @56
    on0eln0
    syl
    mpbird
    @53
    @56
    omword1
    syl21anc
    @52
    @57
    @5
    cZ
    @52
    vz
    cA
    cB
    @49
    cS
    vk
    cG
    @48
    cep
    coi
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    @77
    cfv
    #
    coe
    co
    @78
    cG
    cfv
    comu
    co
    vz
    cv
    coa
    co
    cmpt2
    c0
    cseqom
    #
    cantnfs.s
    @62
    @64
    @77
    eqid
    wph
    @68
    @50
    cantnf.g
    adantr
    @79
    eqid
    @70
    cantnfle
    wph
    @5
    cZ
    wceq
    @50
    cantnf.v
    adantr
    sseqtrd
    sstrd
    wph
    @21
    @50
    @43
    adantr
    @52
    @58
    @15
    @55
    @21
    wa
    @54
    wi
    @72
    wph
    @15
    @50
    @35
    adantr
    @53
    cZ
    @3
    ontr2
    syl2anc
    mp2and
    @52
    @61
    @19
    @24
    @51
    @54
    wb
    @71
    wph
    @19
    @50
    @34
    adantr
    wph
    @24
    @50
    @47
    adantr
    @49
    cX
    cA
    oeord
    syl3anc
    mpbird
    ex
    ssrdv
    cantnf.f
    cantnfp1
    #
    simprd
    wph
    @5
    cZ
    @4
    coa
    cantnf.v
    oveq2d
    @44
    3eqtrd
    wph
    @0
    cS
    wfn
    #
    @8
    @1
    @2
    wcel
    wph
    cS
    @11
    @0
    wf
    @81
    wph
    cA
    cB
    cS
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnff
    cS
    @11
    @0
    ffn
    syl
    wph
    @8
    @9
    @80
    simpld
    cS
    cF
    @0
    fnfvelrn
    syl2anc
    eqeltrrd
end
