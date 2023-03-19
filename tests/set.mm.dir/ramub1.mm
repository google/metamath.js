include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cram.mm"
include "caddc.mm"
include "cfn.mm"
include "eqid.mm"
include "nnnn0d.mm"
include "cn.mm"
include "wf.mm"
include "wss.mm"
include "nnssnn0.mm"
include "fss.mm"
include "sylancl.mm"
include "wcel.mm"
include "peano2nn0.mm"
include "syl.mm"
include "wa.mm"
include "wex.mm"
include "cle.mm"
include "wbr.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "simprl.mm"
include "adantr.mm"
include "nn0p1nn.mm"
include "eqeltrd.mm"
include "wb.mm"
include "vex.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "hashnncl.mm"
include "mpbid.mm"
include "n0.mm"
include "sylib.mm"
include "cdif.mm"
include "cun.mm"
include "cmpt.mm"
include "adantrr.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "ramub1lem2.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "ramub2.mm"

theorem ramub1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cF: class F
  let cG: class G
  let cM: class M
  let vu: setvar u
  let cD: class D
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let cW: class W
  let cS: class S
  let cV: class V
  let cC: class C
  let cH: class H
  let cK: class K
  let cE: class E
  let cX: class X
  assume ramub1.m: |- ( ph -> M e. NN )
  assume ramub1.r: |- ( ph -> R e. Fin )
  assume ramub1.f: |- ( ph -> F : R --> NN )
  assume ramub1.g: |- G = ( x e. R |-> ( M Ramsey ( y e. R |-> if ( y = x , ( ( F ` x ) - 1 ) , ( F ` y ) ) ) ) )
  assume ramub1.1: |- ( ph -> G : R --> NN0 )
  assume ramub1.2: |- ( ph -> ( ( M - 1 ) Ramsey G ) e. NN0 )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint G x
  disjoint G y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint u x
  disjoint D u
  disjoint D x
  disjoint c d
  disjoint c f
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint d f
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a i
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint M a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b i
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint d i
  disjoint M d
  disjoint f i
  disjoint M f
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint G a
  disjoint G c
  disjoint G d
  disjoint G f
  disjoint G i
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G z
  disjoint R c
  disjoint R d
  disjoint R f
  disjoint R s
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint W a
  disjoint W i
  disjoint W u
  disjoint c ph
  disjoint d ph
  disjoint f ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S a
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V a
  disjoint V i
  disjoint V x
  disjoint V z
  disjoint C c
  disjoint C d
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H c
  disjoint H d
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K c
  disjoint K d
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint E x
  disjoint E z
  disjoint X a
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( M Ramsey F ) <_ ( ( ( M - 1 ) Ramsey G ) + 1 ) )

  proof
    wph
    vz
    va
    vi
    cvv
    cn0
    vb
    cv
    chash
    cfv
    vi
    cv
    wceq
    vb
    va
    cv
    cpw
    crab
    cmpt2
    #
    cR
    vf
    vi
    cF
    cM
    cM
    c1
    cmin
    co
    #
    cG
    cram
    co
    #
    c1
    caddc
    co
    #
    cfn
    vs
    va
    vb
    vc
    @0
    eqid
    #
    wph
    cM
    ramub1.m
    nnnn0d
    ramub1.r
    wph
    cR
    cn
    cF
    wf
    #
    cn
    cn0
    wss
    cR
    cn0
    cF
    wf
    ramub1.f
    nnssnn0
    cR
    cn
    cn0
    cF
    fss
    sylancl
    wph
    @2
    cn0
    wcel
    #
    @3
    cn0
    wcel
    ramub1.2
    @2
    peano2nn0
    syl
    wph
    vs
    cv
    #
    chash
    cfv
    #
    @3
    wceq
    #
    @7
    cM
    @0
    co
    cR
    vf
    cv
    #
    wf
    #
    wa
    #
    wa
    #
    vw
    cv
    #
    @7
    wcel
    #
    vw
    wex
    #
    vc
    cv
    #
    cF
    cfv
    vz
    cv
    #
    chash
    cfv
    cle
    wbr
    @18
    cM
    @0
    co
    @10
    ccnv
    @17
    csn
    cima
    wss
    wa
    vz
    @7
    cpw
    wrex
    vc
    cR
    wrex
    #
    @13
    @7
    c0
    wne
    #
    @16
    @13
    @8
    cn
    wcel
    #
    @20
    @13
    @8
    @3
    cn
    wph
    @9
    @11
    simprl
    @13
    @6
    @3
    cn
    wcel
    wph
    @6
    @12
    ramub1.2
    adantr
    @2
    nn0p1nn
    syl
    eqeltrd
    #
    @13
    @7
    cfn
    wcel
    #
    @21
    @20
    wb
    @13
    @8
    cn0
    wcel
    #
    @23
    @13
    @8
    @22
    nnnn0d
    @7
    cvv
    wcel
    @23
    @24
    wb
    vs
    vex
    @7
    cvv
    hashclb
    ax-mp
    sylibr
    #
    @7
    hashnncl
    syl
    mpbid
    vw
    @7
    n0
    sylib
    @13
    @15
    @19
    vw
    wph
    @12
    @15
    @19
    wph
    @12
    @15
    wa
    #
    wa
    vx
    vy
    vz
    vu
    @0
    cR
    @7
    vi
    cF
    cG
    vv
    @7
    @14
    csn
    #
    cdif
    @1
    @0
    co
    #
    vv
    cv
    #
    @27
    cun
    #
    @10
    cfv
    #
    cmpt
    @10
    cM
    @14
    va
    vb
    vc
    wph
    cM
    cn
    wcel
    @26
    ramub1.m
    adantr
    wph
    cR
    cfn
    wcel
    @26
    ramub1.r
    adantr
    wph
    @5
    @26
    ramub1.f
    adantr
    ramub1.g
    wph
    cR
    cn0
    cG
    wf
    @26
    ramub1.1
    adantr
    wph
    @6
    @26
    ramub1.2
    adantr
    @4
    wph
    @12
    @23
    @15
    @25
    adantrr
    wph
    @9
    @11
    @15
    simprll
    wph
    @9
    @11
    @15
    simprlr
    wph
    @12
    @15
    simprr
    vv
    vu
    @28
    @31
    vu
    cv
    #
    @27
    cun
    #
    @10
    cfv
    @29
    @32
    wceq
    @30
    @33
    @10
    @29
    @32
    @27
    uneq1
    fveq2d
    cbvmptv
    ramub1lem2
    expr
    exlimdv
    mpd
    ramub2
end
