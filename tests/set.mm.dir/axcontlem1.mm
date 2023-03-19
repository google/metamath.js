include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "weq.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "adantl.mm"
include "fveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeqan12d.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "eqtri.mm"

theorem axcontlem1
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cD: class D
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cN: class N
  let cZ: class Z
  let vs: setvar s
  assume axcontlem1.1: |- F = { <. x , t >. | ( x e. D /\ ( t e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( x ` i ) = ( ( ( 1 - t ) x. ( Z ` i ) ) + ( t x. ( U ` i ) ) ) ) ) }

  disjoint D s
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint i j
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint N i
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint N j
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint U i
  disjoint U j
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint Z i
  disjoint Z j
  disjoint Z s
  disjoint Z t
  disjoint Z x
  disjoint Z y
  assert |- F = { <. y , s >. | ( y e. D /\ ( s e. ( 0 [,) +oo ) /\ A. j e. ( 1 ... N ) ( y ` j ) = ( ( ( 1 - s ) x. ( Z ` j ) ) + ( s x. ( U ` j ) ) ) ) ) }

  proof
    cF
    vx
    cv
    #
    cD
    wcel
    #
    vt
    cv
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    vi
    cv
    #
    @0
    cfv
    #
    c1
    @2
    cmin
    co
    #
    @5
    cZ
    cfv
    #
    cmul
    co
    #
    @2
    @5
    cU
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    wa
    #
    wa
    #
    vx
    vt
    copab
    vy
    cv
    #
    cD
    wcel
    #
    vs
    cv
    #
    @3
    wcel
    #
    vj
    cv
    #
    @18
    cfv
    #
    c1
    @20
    cmin
    co
    #
    @22
    cZ
    cfv
    #
    cmul
    co
    #
    @20
    @22
    cU
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vj
    @14
    wral
    #
    wa
    #
    wa
    #
    vy
    vs
    copab
    axcontlem1.1
    @17
    @33
    vx
    vt
    vy
    vs
    vx
    vy
    weq
    #
    vt
    vs
    weq
    #
    wa
    #
    @1
    @19
    @16
    @32
    @34
    @1
    @19
    wb
    @35
    @0
    @18
    cD
    eleq1
    adantr
    @36
    @4
    @21
    @15
    @31
    @35
    @4
    @21
    wb
    @34
    @2
    @20
    @3
    eleq1
    adantl
    @36
    @15
    @5
    @18
    cfv
    #
    @24
    @8
    cmul
    co
    #
    @20
    @10
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @14
    wral
    @31
    @36
    @13
    @41
    vi
    @14
    @34
    @35
    @6
    @37
    @12
    @40
    @5
    @0
    @18
    fveq1
    @35
    @9
    @38
    @11
    @39
    caddc
    @35
    @7
    @24
    @8
    cmul
    @2
    @20
    c1
    cmin
    oveq2
    oveq1d
    @2
    @20
    @10
    cmul
    oveq1
    oveq12d
    eqeqan12d
    ralbidv
    @41
    @30
    vi
    vj
    @14
    vi
    vj
    weq
    #
    @37
    @23
    @40
    @29
    @5
    @22
    @18
    fveq2
    @42
    @38
    @26
    @39
    @28
    caddc
    @42
    @8
    @25
    @24
    cmul
    @5
    @22
    cZ
    fveq2
    oveq2d
    @42
    @10
    @27
    @20
    cmul
    @5
    @22
    cU
    fveq2
    oveq2d
    oveq12d
    eqeq12d
    cbvralv
    syl6bb
    anbi12d
    anbi12d
    cbvopabv
    eqtri
end
