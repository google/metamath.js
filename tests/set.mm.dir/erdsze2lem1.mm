include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "wf1.mm"
include "crn.mm"
include "clt.mm"
include "wiso.mm"
include "wex.mm"
include "cdom.mm"
include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wceq.mm"
include "cn0.mm"
include "cmin.mm"
include "cmul.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0mulcld.mm"
include "syl5eqel.mm"
include "peano2nn0.mm"
include "hashfz1.mm"
include "3syl.mm"
include "adantr.mm"
include "wb.mm"
include "hashcl.mm"
include "nn0ltp1le.mm"
include "syl2an.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "fzfid.mm"
include "simpr.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "wn.mm"
include "isinffi.mm"
include "cvv.mm"
include "cr.mm"
include "reex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "brdomg.mm"
include "mpbird.mm"
include "pm2.61dan.mm"
include "domeng.mm"
include "wor.mm"
include "simprr.mm"
include "sstrd.mm"
include "ltso.mm"
include "soss.mm"
include "mpisyl.mm"
include "simprl.mm"
include "enfi.mm"
include "fz1iso.mm"
include "wf1o.mm"
include "isof1o.mm"
include "adantl.mm"
include "hashen.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "f1oeq2.mm"
include "f1of1.mm"
include "simplrr.mm"
include "f1ss.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "isoeq5.mm"
include "4syl.mm"
include "isoeq4.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem erdsze2lem1
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  assume erdsze2.r: |- ( ph -> R e. NN )
  assume erdsze2.s: |- ( ph -> S e. NN )
  assume erdsze2.f: |- ( ph -> F : A -1-1-> RR )
  assume erdsze2.a: |- ( ph -> A C_ RR )
  assume erdsze2lem.n: |- N = ( ( R - 1 ) x. ( S - 1 ) )
  assume erdsze2lem.l: |- ( ph -> N < ( # ` A ) )

  disjoint A f
  disjoint F f
  disjoint R f
  disjoint S f
  disjoint N f
  disjoint f ph
  disjoint f s
  disjoint f t
  disjoint s t
  disjoint A s
  disjoint A t
  disjoint F s
  disjoint F t
  disjoint s x
  disjoint s y
  disjoint G s
  disjoint t x
  disjoint t y
  disjoint G t
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint R s
  disjoint R t
  disjoint S s
  disjoint S t
  disjoint f x
  disjoint f y
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint ph s
  disjoint ph t
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. f ( f : ( 1 ... ( N + 1 ) ) -1-1-> A /\ f Isom < , < ( ( 1 ... ( N + 1 ) ) , ran f ) ) )

  proof
    wph
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    vs
    cv
    #
    cen
    wbr
    #
    @2
    cA
    wss
    #
    wa
    #
    @1
    cA
    vf
    cv
    #
    wf1
    #
    @1
    @6
    crn
    #
    clt
    clt
    @6
    wiso
    #
    wa
    #
    vf
    wex
    #
    vs
    wph
    @1
    cA
    cdom
    wbr
    #
    @5
    vs
    wex
    #
    wph
    cA
    cfn
    wcel
    #
    @12
    wph
    @14
    wa
    #
    @1
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cle
    wbr
    #
    @12
    @15
    @16
    @0
    @17
    cle
    wph
    @16
    @0
    wceq
    #
    @14
    wph
    cN
    cn0
    wcel
    #
    @0
    cn0
    wcel
    @19
    wph
    cN
    cR
    c1
    cmin
    co
    #
    cS
    c1
    cmin
    co
    #
    cmul
    co
    cn0
    erdsze2lem.n
    wph
    @21
    @22
    wph
    cR
    cn
    wcel
    @21
    cn0
    wcel
    erdsze2.r
    cR
    nnm1nn0
    syl
    wph
    cS
    cn
    wcel
    @22
    cn0
    wcel
    erdsze2.s
    cS
    nnm1nn0
    syl
    nn0mulcld
    syl5eqel
    #
    cN
    peano2nn0
    @0
    hashfz1
    3syl
    #
    adantr
    @15
    cN
    @17
    clt
    wbr
    #
    @0
    @17
    cle
    wbr
    #
    wph
    @25
    @14
    erdsze2lem.l
    adantr
    wph
    @20
    @17
    cn0
    wcel
    @25
    @26
    wb
    @14
    @23
    cA
    hashcl
    cN
    @17
    nn0ltp1le
    syl2an
    mpbid
    eqbrtrd
    @15
    @1
    cfn
    wcel
    #
    @14
    @18
    @12
    wb
    @15
    c1
    @0
    fzfid
    wph
    @14
    simpr
    @1
    cA
    cfn
    hashdom
    syl2anc
    mpbid
    wph
    @14
    wn
    #
    wa
    #
    @12
    @7
    vf
    wex
    #
    @29
    @28
    @27
    @30
    wph
    @28
    simpr
    @29
    c1
    @0
    fzfid
    cA
    @1
    vf
    isinffi
    syl2anc
    @29
    cA
    cvv
    wcel
    #
    @12
    @30
    wb
    wph
    @31
    @28
    wph
    cA
    cr
    wss
    #
    cr
    cvv
    wcel
    @31
    erdsze2.a
    reex
    cA
    cr
    cvv
    ssexg
    sylancl
    #
    adantr
    @1
    cA
    cvv
    vf
    brdomg
    syl
    mpbird
    pm2.61dan
    wph
    @31
    @12
    @13
    wb
    @33
    vs
    @1
    cA
    cvv
    domeng
    syl
    mpbid
    wph
    @5
    wa
    #
    c1
    @2
    chash
    cfv
    #
    cfz
    co
    #
    @2
    clt
    clt
    @6
    wiso
    #
    vf
    wex
    #
    @11
    @34
    @2
    clt
    wor
    #
    @2
    cfn
    wcel
    #
    @38
    @34
    @2
    cr
    wss
    cr
    clt
    wor
    @39
    @34
    @2
    cA
    cr
    wph
    @3
    @4
    simprr
    wph
    @32
    @5
    erdsze2.a
    adantr
    sstrd
    ltso
    @2
    cr
    clt
    soss
    mpisyl
    @34
    @27
    @40
    @34
    c1
    @0
    fzfid
    #
    @34
    @3
    @27
    @40
    wb
    wph
    @3
    @4
    simprl
    #
    @1
    @2
    enfi
    syl
    mpbid
    #
    @2
    clt
    vf
    fz1iso
    syl2anc
    @34
    @37
    @10
    vf
    @34
    @37
    @10
    @34
    @37
    wa
    #
    @7
    @9
    @44
    @1
    @2
    @6
    wf1
    #
    @4
    @7
    @44
    @1
    @2
    @6
    wf1o
    #
    @45
    @44
    @36
    @2
    @6
    wf1o
    #
    @46
    @37
    @47
    @34
    @36
    @2
    clt
    clt
    @6
    isof1o
    adantl
    #
    @44
    @36
    @1
    wceq
    #
    @47
    @46
    wb
    @44
    @35
    @0
    c1
    cfz
    @34
    @35
    @0
    wceq
    @37
    @34
    @16
    @35
    @0
    @34
    @16
    @35
    wceq
    #
    @3
    @42
    @34
    @27
    @40
    @50
    @3
    wb
    @41
    @43
    @1
    @2
    hashen
    syl2anc
    mpbird
    wph
    @19
    @5
    @24
    adantr
    eqtr3d
    adantr
    oveq2d
    #
    @36
    @1
    @2
    @6
    f1oeq2
    syl
    mpbid
    @1
    @2
    @6
    f1of1
    syl
    wph
    @3
    @4
    @37
    simplrr
    @1
    @2
    cA
    @6
    f1ss
    syl2anc
    @44
    @36
    @8
    clt
    clt
    @6
    wiso
    #
    @9
    @44
    @52
    @37
    @34
    @37
    simpr
    @44
    @47
    @36
    @2
    @6
    wfo
    @8
    @2
    wceq
    @52
    @37
    wb
    @48
    @36
    @2
    @6
    f1ofo
    @36
    @2
    @6
    forn
    @36
    @8
    @2
    clt
    clt
    @6
    isoeq5
    4syl
    mpbird
    @44
    @49
    @52
    @9
    wb
    @51
    @36
    @8
    @1
    clt
    clt
    @6
    isoeq4
    syl
    mpbid
    jca
    ex
    eximdv
    mpd
    exlimddv
end
