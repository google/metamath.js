include "cv.mm"
include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "wcel.mm"
include "wrex.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "con0.mm"
include "wss.mm"
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
include "omcl.mm"
include "simp3d.mm"
include "oaword1.mm"
include "c0.mm"
include "wne.mm"
include "dif1o.mm"
include "simprbi.mm"
include "wb.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "omword1.mm"
include "syl21anc.mm"
include "sseldd.mm"
include "simprd.mm"
include "eleqtrd.mm"
include "wf.mm"
include "wfn.mm"
include "cantnff.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "3syl.mm"
include "mpbid.mm"
include "cif.mm"
include "cmpt.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "cantnflem3.mm"
include "rexlimddv.mm"

theorem cantnflem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
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
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cD: class D
  let cM: class M
  let cF: class F
  let cG: class G
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

  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
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
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint T c
  disjoint S c
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c t
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
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
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
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint b f
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint d f
  disjoint d h
  disjoint d k
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A k
  disjoint A n
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint M x
  disjoint M y
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint Z g
  disjoint Z t
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
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
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint Y k
  disjoint Y t
  disjoint X k
  disjoint X t
  disjoint X u
  assert |- ( ph -> C e. ran ( A CNF B ) )

  proof
    wph
    vg
    cv
    #
    cA
    cB
    ccnf
    co
    #
    cfv
    cZ
    wceq
    #
    cC
    @1
    crn
    #
    wcel
    vg
    cS
    wph
    cZ
    @3
    wcel
    #
    @2
    vg
    cS
    wrex
    #
    wph
    cC
    @3
    cZ
    cantnf.s
    wph
    cZ
    cA
    cX
    coe
    co
    #
    cY
    comu
    co
    #
    cZ
    coa
    co
    #
    cC
    wph
    @7
    @8
    cZ
    wph
    @7
    con0
    wcel
    #
    cZ
    con0
    wcel
    #
    @7
    @8
    wss
    wph
    @6
    con0
    wcel
    #
    cY
    con0
    wcel
    #
    @9
    wph
    cA
    con0
    wcel
    #
    cX
    con0
    wcel
    #
    @11
    cantnfs.a
    wph
    @14
    cY
    cA
    c1o
    cdif
    wcel
    #
    cZ
    @6
    wcel
    #
    wph
    @14
    @15
    @16
    w3a
    #
    @8
    cC
    wceq
    #
    wph
    cA
    con0
    c2o
    cdif
    wcel
    cC
    con0
    c1o
    cdif
    wcel
    wa
    #
    @17
    @18
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
    @19
    @20
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
    @21
    @22
    @23
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
    cA
    cX
    oecl
    syl2anc
    #
    wph
    @13
    cY
    cA
    wcel
    #
    @12
    cantnfs.a
    wph
    cY
    cA
    c1o
    wph
    @14
    @15
    @16
    @25
    simp2d
    #
    eldifad
    cA
    cY
    onelon
    syl2anc
    #
    @6
    cY
    omcl
    syl2anc
    wph
    @11
    @16
    @10
    @26
    wph
    @14
    @15
    @16
    @25
    simp3d
    #
    @6
    cZ
    onelon
    syl2anc
    @7
    cZ
    oaword1
    syl2anc
    wph
    @6
    @7
    cZ
    wph
    @11
    @12
    c0
    cY
    wcel
    #
    @6
    @7
    wss
    @26
    @29
    wph
    @31
    cY
    c0
    wne
    #
    wph
    @15
    @32
    @28
    @15
    @27
    @32
    cY
    cA
    dif1o
    simprbi
    syl
    wph
    @12
    @31
    @32
    wb
    @29
    cY
    on0eln0
    syl
    mpbird
    @6
    cY
    omword1
    syl21anc
    @30
    sseldd
    sseldd
    wph
    @17
    @18
    @24
    simprd
    eleqtrd
    sseldd
    wph
    cS
    cA
    cB
    coe
    co
    #
    @1
    wf
    @1
    cS
    wfn
    @4
    @5
    wb
    wph
    cA
    cB
    cS
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnff
    cS
    @33
    @1
    ffn
    vg
    cS
    cZ
    @1
    fvelrnb
    3syl
    mpbid
    wph
    @0
    cS
    wcel
    #
    @2
    wa
    #
    wa
    vx
    vy
    vz
    vw
    vt
    cA
    cB
    cC
    cP
    cS
    cT
    vt
    cB
    vt
    cv
    #
    cX
    wceq
    cY
    @36
    @0
    cfv
    cif
    cmpt
    #
    @0
    cX
    cY
    cZ
    va
    vb
    vc
    vd
    cantnfs.s
    wph
    @13
    @35
    cantnfs.a
    adantr
    wph
    cB
    con0
    wcel
    @35
    cantnfs.b
    adantr
    oemapval.t
    wph
    cC
    @33
    wcel
    @35
    cantnf.c
    adantr
    wph
    cC
    @3
    wss
    @35
    cantnf.s
    adantr
    wph
    c0
    cC
    wcel
    @35
    cantnf.e
    adantr
    cantnf.x
    cantnf.p
    cantnf.y
    cantnf.z
    wph
    @34
    @2
    simprl
    wph
    @34
    @2
    simprr
    @37
    eqid
    cantnflem3
    rexlimddv
end
