include "cc0.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cseq.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "wss.mm"
include "cabs.mm"
include "ccnv.mm"
include "cicc.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "syl6ss.mm"
include "adantr.mm"
include "resmptd.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "simplr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "pserval2.mm"
include "syl2anc.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "expcl.mm"
include "adantll.mm"
include "mulcld.mm"
include "sylan2.mm"
include "fsumser.mm"
include "mpteq2dva.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "eqid.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "fzfid.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "cnmptc.mm"
include "expcn.mm"
include "syl.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "fsumcn.mm"
include "cncfcn1.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"
include "rescncf.mm"
include "sylc.mm"
include "fmptd.mm"
include "pserulm.mm"
include "ulmcn.mm"

theorem psercn2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume pserulm.h: |- H = ( i e. NN0 |-> ( y e. S |-> ( seq 0 ( + , ( G ` y ) ) ` i ) ) )
  assume pserulm.m: |- ( ph -> M e. RR )
  assume pserulm.l: |- ( ph -> M < R )
  assume pserulm.y: |- ( ph -> S C_ ( `' abs " ( 0 [,] M ) ) )

  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint M i
  disjoint M j
  disjoint M y
  disjoint i x
  disjoint i r
  disjoint G i
  disjoint G j
  disjoint G r
  disjoint G y
  disjoint S i
  disjoint S j
  disjoint S y
  disjoint i ph
  disjoint j ph
  disjoint ph y
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint M k
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint S a
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S k
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F a
  disjoint F f
  disjoint F z
  disjoint a ph
  disjoint f ph
  disjoint k ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ph -> F e. ( S -cn-> CC ) )

  proof
    wph
    cS
    cH
    cF
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    vi
    cn0
    vy
    cS
    vi
    cv
    #
    caddc
    vy
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    cfv
    #
    cmpt
    #
    cS
    cc
    ccncf
    co
    #
    cH
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    vy
    cc
    @3
    cmpt
    #
    cS
    cres
    #
    @4
    @5
    @7
    vy
    cc
    cS
    @3
    wph
    cS
    cc
    wss
    #
    @6
    wph
    cS
    cabs
    ccnv
    cc0
    cM
    cicc
    co
    #
    cima
    #
    cc
    pserulm.y
    @12
    cabs
    cdm
    cc
    cabs
    @11
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    syl6ss
    adantr
    #
    resmptd
    @7
    @10
    @8
    cc
    cc
    ccncf
    co
    #
    wcel
    @9
    @5
    wcel
    @13
    @7
    vy
    cc
    cc0
    @0
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    @1
    @16
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    @8
    @14
    @7
    vy
    cc
    @20
    @3
    @7
    @1
    cc
    wcel
    #
    wa
    #
    @19
    vk
    @2
    cc0
    @0
    @23
    @16
    @15
    wcel
    #
    wa
    @22
    @16
    cn0
    wcel
    #
    @16
    @2
    cfv
    @19
    wceq
    @7
    @22
    @24
    simplr
    @24
    @25
    @23
    @16
    @0
    elfznn0
    #
    adantl
    vx
    cA
    vn
    cG
    @16
    @1
    pserf.g
    pserval2
    syl2anc
    @7
    @0
    cc0
    cuz
    cfv
    #
    wcel
    @22
    @7
    @0
    cn0
    @27
    wph
    @6
    simpr
    nn0uz
    syl6eleq
    adantr
    @24
    @23
    @25
    @19
    cc
    wcel
    @26
    @23
    @25
    wa
    @17
    @18
    @7
    @25
    @17
    cc
    wcel
    #
    @22
    @7
    cn0
    cc
    @16
    cA
    wph
    cn0
    cc
    cA
    wf
    #
    @6
    pserf.a
    adantr
    #
    ffvelrnda
    adantlr
    @22
    @25
    @18
    cc
    wcel
    @7
    @1
    @16
    expcl
    adantll
    mulcld
    sylan2
    fsumser
    mpteq2dva
    @7
    @21
    ccnfld
    ctopn
    cfv
    #
    @31
    ccn
    co
    #
    @14
    @7
    vy
    @15
    @19
    vk
    @31
    @31
    cc
    @31
    eqid
    #
    @31
    cc
    ctopon
    cfv
    wcel
    #
    @7
    @31
    @33
    cnfldtopon
    #
    a1i
    @7
    cc0
    @0
    fzfid
    @7
    @24
    wa
    #
    vy
    @17
    @18
    cmul
    @31
    @31
    @31
    @31
    cc
    @34
    @36
    @35
    a1i
    #
    @36
    vy
    @17
    @31
    @31
    cc
    cc
    @37
    @37
    @7
    @29
    @25
    @28
    @24
    @30
    @26
    cn0
    cc
    @16
    cA
    ffvelrn
    syl2an
    cnmptc
    @36
    @25
    vy
    cc
    @18
    cmpt
    @32
    wcel
    @24
    @25
    @7
    @26
    adantl
    vy
    @31
    @16
    @33
    expcn
    syl
    cmul
    @31
    @31
    ctx
    co
    @31
    ccn
    co
    wcel
    @36
    @31
    @33
    mulcn
    a1i
    cnmpt12f
    fsumcn
    @31
    @33
    cncfcn1
    syl6eleqr
    eqeltrrd
    cc
    cc
    cS
    @8
    rescncf
    sylc
    eqeltrrd
    pserulm.h
    fmptd
    wph
    vx
    vy
    cA
    cR
    cS
    vi
    vj
    vn
    cF
    cG
    cH
    cM
    vr
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    pserulm.h
    pserulm.m
    pserulm.l
    pserulm.y
    pserulm
    ulmcn
end
