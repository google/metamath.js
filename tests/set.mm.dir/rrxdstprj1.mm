include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "cun.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cdif.mm"
include "simplll.mm"
include "simpr.mm"
include "simplr.mm"
include "cmin.mm"
include "cabs.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cfn.mm"
include "simprl.mm"
include "rrxfsupp.mm"
include "simprr.mm"
include "unfi.mm"
include "syl2anc.mm"
include "cr.mm"
include "rrxsuppss.mm"
include "unssd.mm"
include "sselda.mm"
include "rrxf.mm"
include "ffvelrnda.mm"
include "resubcld.mm"
include "resqcld.mm"
include "syldan.mm"
include "sqge0d.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "fsumge1.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "absresq.mm"
include "syl.mm"
include "fsumrecl.mm"
include "fsumge0.mm"
include "resqrtth.mm"
include "3brtr4d.mm"
include "recnd.mm"
include "abscld.mm"
include "resqrtcld.mm"
include "absge0d.mm"
include "sqrtge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "remetdval.mm"
include "rrxmval.mm"
include "3expb.mm"
include "adantlr.mm"
include "syl21anc.mm"
include "simplrl.mm"
include "wss.mm"
include "ssun1.mm"
include "a1i.mm"
include "sscond.mm"
include "ssid.mm"
include "simpl.mm"
include "0red.mm"
include "suppssr.mm"
include "eqeltrd.mm"
include "simplrr.mm"
include "ssun2.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "abs00bd.mm"
include "eqtrd.mm"
include "cme.mm"
include "rrxmet.mm"
include "ad3antrrr.mm"
include "metge0.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "wo.mm"
include "undif.mm"
include "sylib.mm"
include "eleqtrrd.mm"
include "elun.mm"
include "mpjaodan.mm"

theorem rrxdstprj1
  let cA: class A
  let cD: class D
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }
  assume rrxmval.d: |- D = ( dist ` ( RR^ ` I ) )
  assume rrxdstprj1.1: |- M = ( ( abs o. - ) |` ( RR X. RR ) )

  disjoint F h
  disjoint G h
  disjoint I h
  disjoint V h
  disjoint A k
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F x
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h k
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G x
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V f
  disjoint V g
  disjoint V k
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( ( I e. V /\ A e. I ) /\ ( F e. X /\ G e. X ) ) -> ( ( F ` A ) M ( G ` A ) ) <_ ( F D G ) )

  proof
    cI
    cV
    wcel
    #
    cA
    cI
    wcel
    #
    wa
    #
    cF
    cX
    wcel
    #
    cG
    cX
    wcel
    #
    wa
    #
    wa
    #
    cA
    cF
    cc0
    csupp
    co
    #
    cG
    cc0
    csupp
    co
    #
    cun
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    cM
    co
    #
    cF
    cG
    cD
    co
    #
    cle
    wbr
    #
    cA
    cI
    @9
    cdif
    #
    wcel
    #
    @6
    @10
    wa
    @0
    @10
    @5
    @15
    @0
    @1
    @5
    @10
    simplll
    @6
    @10
    simpr
    @2
    @5
    @10
    simplr
    @0
    @10
    wa
    #
    @5
    wa
    #
    @11
    @12
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    vk
    cv
    #
    cF
    cfv
    #
    @22
    cG
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    @13
    @14
    cle
    @19
    @21
    @28
    cle
    wbr
    @21
    c2
    cexp
    co
    #
    @28
    c2
    cexp
    co
    #
    cle
    wbr
    @19
    @20
    c2
    cexp
    co
    #
    @27
    @29
    @30
    cle
    @19
    @9
    @26
    @31
    vk
    cA
    @19
    @7
    cfn
    wcel
    @8
    cfn
    wcel
    @9
    cfn
    wcel
    @19
    vh
    cF
    cI
    cX
    rrxmval.1
    @18
    @3
    @4
    simprl
    #
    rrxfsupp
    @19
    vh
    cG
    cI
    cX
    rrxmval.1
    @18
    @3
    @4
    simprr
    #
    rrxfsupp
    @7
    @8
    unfi
    syl2anc
    #
    @19
    @22
    @9
    wcel
    #
    @22
    cI
    wcel
    #
    @26
    cr
    wcel
    @19
    @9
    cI
    @22
    @19
    @7
    @8
    cI
    @19
    vh
    cF
    cI
    cX
    rrxmval.1
    @32
    rrxsuppss
    @19
    vh
    cG
    cI
    cX
    rrxmval.1
    @33
    rrxsuppss
    unssd
    #
    sselda
    #
    @19
    @36
    wa
    #
    @25
    @39
    @23
    @24
    @19
    cI
    cr
    @22
    cF
    @19
    vh
    cF
    cI
    cX
    rrxmval.1
    @32
    rrxf
    #
    ffvelrnda
    @19
    cI
    cr
    @22
    cG
    @19
    vh
    cG
    cI
    cX
    rrxmval.1
    @33
    rrxf
    #
    ffvelrnda
    resubcld
    #
    resqcld
    syldan
    #
    @19
    @35
    @36
    cc0
    @26
    cle
    wbr
    @38
    @39
    @25
    @42
    sqge0d
    syldan
    #
    @22
    cA
    wceq
    #
    @25
    @20
    c2
    cexp
    @45
    @23
    @11
    @24
    @12
    cmin
    @22
    cA
    cF
    fveq2
    @22
    cA
    cG
    fveq2
    oveq12d
    oveq1d
    @0
    @10
    @5
    simplr
    #
    fsumge1
    @19
    @20
    cr
    wcel
    @29
    @31
    wceq
    @19
    @11
    @12
    @19
    cI
    cr
    cA
    cF
    @40
    @19
    @9
    cI
    cA
    @37
    @46
    sseldd
    #
    ffvelrnd
    #
    @19
    cI
    cr
    cA
    cG
    @41
    @47
    ffvelrnd
    #
    resubcld
    #
    @20
    absresq
    syl
    @19
    @27
    cr
    wcel
    cc0
    @27
    cle
    wbr
    @30
    @27
    wceq
    @19
    @9
    @26
    vk
    @34
    @43
    fsumrecl
    #
    @19
    @9
    @26
    vk
    @34
    @43
    @44
    fsumge0
    #
    @27
    resqrtth
    syl2anc
    3brtr4d
    @19
    @21
    @28
    @19
    @20
    @19
    @20
    @50
    recnd
    #
    abscld
    @19
    @27
    @51
    @52
    resqrtcld
    @19
    @20
    @53
    absge0d
    @19
    @27
    @51
    @52
    sqrtge0d
    le2sqd
    mpbird
    @19
    @11
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @13
    @21
    wceq
    #
    @48
    @49
    @11
    @12
    cM
    rrxdstprj1.1
    remetdval
    #
    syl2anc
    @0
    @5
    @14
    @28
    wceq
    #
    @10
    @0
    @3
    @4
    @58
    cD
    vh
    vk
    cF
    cG
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmval
    3expb
    adantlr
    3brtr4d
    syl21anc
    @6
    @17
    wa
    #
    @13
    cc0
    @14
    cle
    @59
    @13
    @21
    cc0
    @59
    @54
    @55
    @56
    @59
    @11
    cc0
    cr
    @59
    @0
    @3
    cA
    cI
    @7
    cdif
    #
    wcel
    @11
    cc0
    wceq
    @0
    @1
    @5
    @17
    simplll
    #
    @2
    @3
    @4
    @17
    simplrl
    #
    @6
    @16
    @60
    cA
    @6
    @7
    @9
    cI
    @7
    @9
    wss
    @6
    @7
    @8
    ssun1
    a1i
    sscond
    sselda
    @0
    @3
    wa
    #
    cI
    cr
    cr
    cF
    cV
    @7
    cA
    cc0
    @63
    vh
    cF
    cI
    cX
    rrxmval.1
    @0
    @3
    simpr
    rrxf
    @7
    @7
    wss
    @63
    @7
    ssid
    a1i
    @0
    @3
    simpl
    @63
    0red
    suppssr
    syl21anc
    #
    @59
    0red
    #
    eqeltrd
    @59
    @12
    cc0
    cr
    @59
    @0
    @4
    cA
    cI
    @8
    cdif
    #
    wcel
    @12
    cc0
    wceq
    @61
    @2
    @3
    @4
    @17
    simplrr
    #
    @6
    @16
    @66
    cA
    @6
    @8
    @9
    cI
    @8
    @9
    wss
    @6
    @8
    @7
    ssun2
    a1i
    sscond
    sselda
    @0
    @4
    wa
    #
    cI
    cr
    cr
    cG
    cV
    @8
    cA
    cc0
    @68
    vh
    cG
    cI
    cX
    rrxmval.1
    @0
    @4
    simpr
    rrxf
    @8
    @8
    wss
    @68
    @8
    ssid
    a1i
    @0
    @4
    simpl
    @68
    0red
    suppssr
    syl21anc
    #
    @65
    eqeltrd
    @57
    syl2anc
    @59
    @20
    @59
    @20
    cc0
    cc0
    cmin
    co
    cc0
    @59
    @11
    cc0
    @12
    cc0
    cmin
    @64
    @69
    oveq12d
    0m0e0
    syl6eq
    abs00bd
    eqtrd
    @59
    cD
    cX
    cme
    cfv
    wcel
    #
    @3
    @4
    cc0
    @14
    cle
    wbr
    @0
    @70
    @1
    @5
    @17
    cD
    vh
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmet
    ad3antrrr
    @62
    @67
    cF
    cG
    cD
    cX
    metge0
    syl3anc
    eqbrtrd
    @6
    cA
    @9
    @16
    cun
    #
    wcel
    @10
    @17
    wo
    @6
    cA
    cI
    @71
    @0
    @1
    @5
    simplr
    @6
    @9
    cI
    wss
    @71
    cI
    wceq
    @6
    @7
    @8
    cI
    @6
    vh
    cF
    cI
    cX
    rrxmval.1
    @2
    @3
    @4
    simprl
    rrxsuppss
    @6
    vh
    cG
    cI
    cX
    rrxmval.1
    @2
    @3
    @4
    simprr
    rrxsuppss
    unssd
    @9
    cI
    undif
    sylib
    eleqtrrd
    cA
    @9
    @16
    elun
    sylib
    mpjaodan
end
