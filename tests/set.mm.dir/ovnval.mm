include "cr.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cn.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wa.mm"
include "cxp.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cfn.mm"
include "covoln.mm"
include "cvv.mm"
include "df-ovoln.mm"
include "a1i.mm"
include "oveq2.mm"
include "pweqd.mm"
include "eqeq1.mm"
include "oveq1d.mm"
include "ixpeq1.mm"
include "iuneq2d.mm"
include "sseq2d.mm"
include "wcel.mm"
include "simpl.mm"
include "prodeq1d.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "ovex.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmptd.mm"

theorem ovnval
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cX: class X
  let vx: setvar x
  assume ovnval.1: |- ( ph -> X e. Fin )

  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X y
  disjoint X z
  disjoint i j
  disjoint i k
  disjoint i y
  disjoint i z
  disjoint j k
  disjoint j y
  disjoint j z
  disjoint k y
  disjoint k z
  disjoint y z
  disjoint X x
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( voln* ` X ) = ( y e. ~P ( RR ^m X ) |-> if ( X = (/) , 0 , inf ( { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( y C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) } , RR* , < ) ) ) )

  proof
    wph
    vx
    cX
    vy
    cr
    vx
    cv
    #
    cmap
    co
    #
    cpw
    #
    @0
    c0
    wceq
    #
    cc0
    vy
    cv
    #
    vj
    cn
    vk
    @0
    vk
    cv
    cico
    vj
    cv
    #
    vi
    cv
    cfv
    ccom
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    vz
    cv
    #
    vj
    cn
    @0
    @6
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    cr
    cr
    cxp
    #
    @0
    cmap
    co
    #
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cif
    #
    cmpt
    #
    vy
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cX
    c0
    wceq
    #
    cc0
    @4
    vj
    cn
    vk
    cX
    @6
    cixp
    #
    ciun
    #
    wss
    #
    @10
    vj
    cn
    cX
    @11
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    @17
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cif
    #
    cmpt
    #
    cfn
    covoln
    cvv
    covoln
    vx
    cfn
    @24
    cmpt
    wceq
    wph
    vx
    vy
    vz
    vi
    vj
    vk
    df-ovoln
    a1i
    @0
    cX
    wceq
    #
    @24
    @42
    wceq
    wph
    @43
    vy
    @2
    @23
    @26
    @41
    @43
    @1
    @25
    @0
    cX
    cr
    cmap
    oveq2
    pweqd
    @43
    @3
    @27
    @22
    @40
    cc0
    @0
    cX
    c0
    eqeq1
    @43
    cxr
    @21
    @39
    clt
    @43
    @20
    @38
    vz
    cxr
    @43
    @16
    @35
    vi
    @19
    @37
    @43
    @18
    @36
    cn
    cmap
    @0
    cX
    @17
    cmap
    oveq2
    oveq1d
    @43
    @9
    @30
    @15
    @34
    @43
    @8
    @29
    @4
    @43
    vj
    cn
    @7
    @28
    vk
    @0
    cX
    @6
    ixpeq1
    iuneq2d
    sseq2d
    @43
    @14
    @33
    @10
    @43
    @13
    @32
    csumge0
    @43
    vj
    cn
    @12
    @31
    @43
    @5
    cn
    wcel
    #
    wa
    @0
    cX
    @11
    vk
    @43
    @44
    simpl
    prodeq1d
    mpteq2dva
    fveq2d
    eqeq2d
    anbi12d
    rexeqbidv
    rabbidv
    infeq1d
    ifbieq2d
    mpteq12dv
    adantl
    ovnval.1
    @42
    cvv
    wcel
    wph
    vy
    @26
    @41
    @25
    cr
    cX
    cmap
    ovex
    pwex
    mptex
    a1i
    fvmptd
end
