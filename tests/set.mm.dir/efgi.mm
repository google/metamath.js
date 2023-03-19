include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "c2o.mm"
include "cop.mm"
include "c1o.mm"
include "cdif.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "wbr.mm"
include "cv.mm"
include "wer.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "id.mm"
include "oveq1.mm"
include "breq12d.mm"
include "2ralbidv.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "oteq1.mm"
include "oteq2.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "sylan9.mm"
include "opeq1.mm"
include "s2eqd.mm"
include "oteq3d.mm"
include "opeq2.mm"
include "difeq2.mm"
include "opeq2d.mm"
include "df-br.mm"
include "syl6bb.mm"
include "rspc2v.mm"
include "adantld.mm"
include "alrimiv.mm"
include "opex.mm"
include "elintab.mm"
include "sylibr.mm"
include "efgval.mm"
include "syl6eleqr.mm"

theorem efgi
  let cA: class A
  let c.sm: class .~
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cL: class L
  let cF: class F
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let cP: class P
  let wph: wff ph
  let vm: setvar m
  let vx: setvar x
  let cM: class M
  let cU: class U
  let vk: setvar k
  let vo: setvar o
  let cT: class T
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )


  assert |- ( ( ( A e. W /\ N e. ( 0 ... ( # ` A ) ) ) /\ ( J e. I /\ K e. 2o ) ) -> A .~ ( A splice <. N , N , <" <. J , K >. <. J , ( 1o \ K ) >. "> >. ) )

  proof
    cA
    cW
    wcel
    #
    cN
    cc0
    cA
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cJ
    cI
    wcel
    cK
    c2o
    wcel
    wa
    #
    wa
    #
    cA
    cA
    cN
    cN
    cJ
    cK
    cop
    #
    cJ
    c1o
    cK
    cdif
    #
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    cop
    #
    c.sm
    wcel
    cA
    @12
    c.sm
    wbr
    @6
    @13
    cW
    vr
    cv
    #
    wer
    #
    vu
    cv
    #
    @16
    vi
    cv
    #
    @17
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    @18
    c1o
    @19
    cdif
    #
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    @14
    wbr
    #
    vb
    c2o
    wral
    va
    cI
    wral
    #
    vi
    cc0
    @16
    chash
    cfv
    #
    cfz
    co
    #
    wral
    #
    vu
    cW
    wral
    #
    wa
    #
    vr
    cab
    cint
    #
    c.sm
    @6
    @32
    @13
    @14
    wcel
    #
    wi
    #
    vr
    wal
    @13
    @33
    wcel
    @6
    @35
    vr
    @6
    @31
    @34
    @15
    @4
    @31
    cA
    cA
    cN
    cN
    @23
    cotp
    #
    csplice
    co
    #
    @14
    wbr
    #
    vb
    c2o
    wral
    va
    cI
    wral
    #
    @5
    @34
    @0
    @31
    cA
    cA
    @24
    csplice
    co
    #
    @14
    wbr
    #
    vb
    c2o
    wral
    va
    cI
    wral
    #
    vi
    @2
    wral
    #
    @3
    @39
    @30
    @43
    vu
    cA
    cW
    @16
    cA
    wceq
    #
    @27
    @42
    vi
    @29
    @2
    @44
    @28
    @1
    cc0
    cfz
    @16
    cA
    chash
    fveq2
    oveq2d
    @44
    @26
    @41
    va
    vb
    cI
    c2o
    @44
    @16
    cA
    @25
    @40
    @14
    @44
    id
    @16
    cA
    @24
    csplice
    oveq1
    breq12d
    2ralbidv
    raleqbidv
    rspcv
    @42
    @39
    vi
    cN
    @2
    @17
    cN
    wceq
    #
    @41
    @38
    va
    vb
    cI
    c2o
    @45
    @40
    @37
    cA
    @14
    @45
    @24
    @36
    cA
    csplice
    @45
    @24
    cN
    @17
    @23
    cotp
    @36
    @17
    cN
    @17
    @23
    oteq1
    @17
    cN
    cN
    @23
    oteq2
    eqtrd
    oveq2d
    breq2d
    2ralbidv
    rspcv
    sylan9
    @38
    @34
    cA
    cA
    cN
    cN
    cJ
    @19
    cop
    #
    cJ
    @21
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    @14
    wbr
    #
    va
    vb
    cJ
    cK
    cI
    c2o
    @18
    cJ
    wceq
    #
    @37
    @50
    cA
    @14
    @52
    @36
    @49
    cA
    csplice
    @52
    @23
    @48
    cN
    cN
    @52
    @20
    @22
    @46
    @47
    @18
    cJ
    @19
    opeq1
    @18
    cJ
    @21
    opeq1
    s2eqd
    oteq3d
    oveq2d
    breq2d
    @19
    cK
    wceq
    #
    @51
    cA
    @12
    @14
    wbr
    @34
    @53
    @50
    @12
    cA
    @14
    @53
    @49
    @11
    cA
    csplice
    @53
    @48
    @10
    cN
    cN
    @53
    @46
    @47
    @7
    @9
    @19
    cK
    cJ
    opeq2
    @53
    @21
    @8
    cJ
    @19
    cK
    c1o
    difeq2
    opeq2d
    s2eqd
    oteq3d
    oveq2d
    breq2d
    cA
    @12
    @14
    df-br
    syl6bb
    rspc2v
    sylan9
    adantld
    alrimiv
    @32
    vr
    @13
    cA
    @12
    opex
    elintab
    sylibr
    vu
    va
    vb
    c.sm
    vi
    cI
    cW
    vr
    efgval.w
    efgval.r
    efgval
    syl6eleqr
    cA
    @12
    c.sm
    df-br
    sylibr
end
