include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "cvv.mm"
include "wcel.mm"
include "mptexg.mm"
include "syl.mm"
include "cmat.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ovexd.mm"
include "cbs.mm"
include "cfn.mm"
include "crg.mm"
include "wceq.mm"
include "eqid.mm"
include "matbas.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "matplusg.mm"
include "gsumpropd.mm"
include "mpt2mpts.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "c0g.mm"
include "xpfi.mm"
include "wa.mm"
include "syl6eleq.mm"
include "eqcomi.mm"
include "jca.mm"
include "adantr.mm"
include "3eltr4d.mm"
include "cfsupp.mm"
include "mpteq2i.mm"
include "3brtr4g.mm"
include "mat0.mm"
include "breqtrrd.mm"
include "frlmgsum.mm"
include "eqtrd.mm"
include "fvex.mm"
include "csbov2g.mm"
include "ax-mp.mm"
include "csbeq2i.mm"
include "csbmpt2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "3eqtrri.mm"
include "eqtr4i.mm"
include "3eqtrd.mm"

theorem matgsum
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let cJ: class J
  let cN: class N
  let cW: class W
  let c.0: class .0.
  let vz: setvar z
  assume matgsum.a: |- A = ( N Mat R )
  assume matgsum.b: |- B = ( Base ` A )
  assume matgsum.z: |- .0. = ( 0g ` A )
  assume matgsum.i: |- ( ph -> N e. Fin )
  assume matgsum.j: |- ( ph -> J e. W )
  assume matgsum.r: |- ( ph -> R e. Ring )
  assume matgsum.f: |- ( ( ph /\ y e. J ) -> ( i e. N , j e. N |-> U ) e. B )
  assume matgsum.w: |- ( ph -> ( y e. J |-> ( i e. N , j e. N |-> U ) ) finSupp .0. )

  disjoint J i
  disjoint J j
  disjoint J y
  disjoint i j
  disjoint i y
  disjoint j y
  disjoint N i
  disjoint N j
  disjoint N y
  disjoint R i
  disjoint R j
  disjoint R y
  disjoint ph y
  disjoint J z
  disjoint i z
  disjoint j z
  disjoint y z
  disjoint N z
  disjoint R z
  disjoint U z
  disjoint ph z
  assert |- ( ph -> ( A gsum ( y e. J |-> ( i e. N , j e. N |-> U ) ) ) = ( i e. N , j e. N |-> ( R gsum ( y e. J |-> U ) ) ) )

  proof
    wph
    cA
    vy
    cJ
    vi
    vj
    cN
    cN
    cU
    cmpt2
    #
    cmpt
    #
    cgsu
    co
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    @1
    cgsu
    co
    #
    vz
    @2
    cR
    vy
    cJ
    vi
    vz
    cv
    #
    c1st
    cfv
    #
    vj
    @5
    c2nd
    cfv
    #
    cU
    csb
    #
    csb
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    vi
    vj
    cN
    cN
    cR
    vy
    cJ
    cU
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    wph
    @1
    cA
    @3
    cvv
    cvv
    cvv
    wph
    cJ
    cW
    wcel
    @1
    cvv
    wcel
    matgsum.j
    vy
    cJ
    @0
    cW
    mptexg
    syl
    cA
    cvv
    wcel
    wph
    cA
    cN
    cR
    cmat
    co
    cvv
    matgsum.a
    cN
    cR
    cmat
    ovex
    eqeltri
    a1i
    wph
    cR
    @2
    cfrlm
    ovexd
    wph
    @3
    cbs
    cfv
    #
    cA
    cbs
    cfv
    #
    wph
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    @16
    @17
    wceq
    #
    matgsum.i
    matgsum.r
    cA
    cR
    @3
    cN
    crg
    matgsum.a
    @3
    eqid
    #
    matbas
    #
    syl2anc
    eqcomd
    wph
    @3
    cplusg
    cfv
    #
    cA
    cplusg
    cfv
    #
    wph
    @18
    @19
    @23
    @24
    wceq
    matgsum.i
    matgsum.r
    cA
    cR
    @3
    cN
    crg
    matgsum.a
    @21
    matplusg
    syl2anc
    eqcomd
    gsumpropd
    wph
    @4
    @3
    vy
    cJ
    vz
    @2
    @9
    cmpt
    #
    cmpt
    #
    cgsu
    co
    @12
    wph
    @1
    @26
    @3
    cgsu
    wph
    vy
    cJ
    @0
    @25
    @0
    @25
    wceq
    wph
    vi
    vj
    vz
    cN
    cN
    cU
    mpt2mpts
    #
    a1i
    mpteq2dv
    oveq2d
    wph
    vz
    vy
    @16
    cR
    @9
    @2
    cJ
    cfn
    cW
    @3
    @3
    c0g
    cfv
    #
    @21
    @16
    eqid
    @28
    eqid
    wph
    @18
    @18
    @2
    cfn
    wcel
    matgsum.i
    matgsum.i
    cN
    cN
    xpfi
    syl2anc
    matgsum.j
    matgsum.r
    wph
    vy
    cv
    cJ
    wcel
    #
    wa
    #
    @0
    @17
    @25
    @16
    @30
    @0
    cB
    @17
    matgsum.f
    matgsum.b
    syl6eleq
    @25
    @0
    wceq
    @30
    @0
    @25
    @27
    eqcomi
    #
    a1i
    @30
    @18
    @19
    wa
    #
    @20
    wph
    @32
    @29
    wph
    @18
    @19
    matgsum.i
    matgsum.r
    jca
    adantr
    @22
    syl
    3eltr4d
    wph
    @26
    cA
    c0g
    cfv
    #
    @28
    cfsupp
    wph
    @1
    c.0
    @26
    @33
    cfsupp
    matgsum.w
    vy
    cJ
    @25
    @0
    @31
    mpteq2i
    c.0
    @33
    matgsum.z
    eqcomi
    3brtr4g
    wph
    @18
    @19
    @28
    @33
    wceq
    matgsum.i
    matgsum.r
    cA
    cR
    @3
    cN
    crg
    matgsum.a
    @21
    mat0
    syl2anc
    breqtrrd
    frlmgsum
    eqtrd
    @12
    @15
    wceq
    wph
    @12
    vz
    @2
    vi
    @6
    vj
    @7
    @14
    csb
    #
    csb
    #
    cmpt
    @15
    vz
    @2
    @11
    @35
    @35
    vi
    @6
    cR
    vj
    @7
    @13
    csb
    #
    cgsu
    co
    #
    csb
    #
    cR
    vi
    @6
    @36
    csb
    #
    cgsu
    co
    #
    @11
    vi
    @6
    @34
    @37
    @7
    cvv
    wcel
    #
    @34
    @37
    wceq
    @5
    c2nd
    fvex
    #
    vj
    @7
    cR
    @13
    cgsu
    cvv
    csbov2g
    ax-mp
    csbeq2i
    @6
    cvv
    wcel
    #
    @38
    @40
    wceq
    @5
    c1st
    fvex
    #
    vi
    @6
    cR
    @36
    cgsu
    cvv
    csbov2g
    ax-mp
    @39
    @10
    cR
    cgsu
    @39
    vi
    @6
    vy
    cJ
    @8
    cmpt
    #
    csb
    #
    @10
    vi
    @6
    @36
    @45
    @41
    @36
    @45
    wceq
    @42
    vj
    vy
    @7
    cvv
    cJ
    cU
    csbmpt2
    ax-mp
    csbeq2i
    @43
    @46
    @10
    wceq
    @44
    vi
    vy
    @6
    cvv
    cJ
    @8
    csbmpt2
    ax-mp
    eqtri
    oveq2i
    3eqtrri
    mpteq2i
    vi
    vj
    vz
    cN
    cN
    @14
    mpt2mpts
    eqtr4i
    a1i
    3eqtrd
end
