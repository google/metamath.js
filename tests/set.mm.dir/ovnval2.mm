include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
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
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cpw.mm"
include "covoln.mm"
include "cvv.mm"
include "ovnval.mm"
include "biidd.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "syl6eqr.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "adantl.mm"
include "wcel.mm"
include "wb.mm"
include "ovexd.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "c0ex.mm"
include "a1i.mm"
include "infeq1i.mm"
include "xrltso.mm"
include "infex.mm"
include "syl5eqel.mm"
include "ifcld.mm"
include "fvmptd.mm"

theorem ovnval2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cX: class X
  let vy: setvar y
  let vx: setvar x
  assume ovnval2.1: |- ( ph -> X e. Fin )
  assume ovnval2.2: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnval2.3: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }

  disjoint A i
  disjoint A z
  disjoint i z
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint A y
  disjoint i y
  disjoint y z
  disjoint M y
  disjoint X y
  disjoint j y
  disjoint k y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` A ) = if ( X = (/) , 0 , inf ( M , RR* , < ) ) )

  proof
    wph
    vy
    cA
    cX
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
    cX
    vk
    cv
    cico
    vj
    cv
    vi
    cv
    cfv
    ccom
    cfv
    #
    cixp
    ciun
    #
    wss
    #
    vz
    cv
    vj
    cn
    cX
    @2
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    wceq
    #
    wa
    #
    vi
    cr
    cr
    cxp
    cX
    cmap
    co
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
    @0
    cc0
    cM
    cxr
    clt
    cinf
    #
    cif
    #
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cX
    covoln
    cfv
    cvv
    wph
    vy
    vz
    vi
    vj
    vk
    cX
    ovnval2.1
    ovnval
    @1
    cA
    wceq
    #
    @11
    @13
    wceq
    wph
    @16
    @0
    @0
    @10
    @12
    cc0
    @16
    @0
    biidd
    @16
    cxr
    @9
    cM
    clt
    @16
    @9
    cA
    @3
    wss
    #
    @5
    wa
    #
    vi
    @7
    wrex
    #
    vz
    cxr
    crab
    #
    cM
    @16
    @8
    @19
    vz
    cxr
    @16
    @6
    @18
    vi
    @7
    @16
    @4
    @17
    @5
    @1
    cA
    @3
    sseq1
    anbi1d
    rexbidv
    rabbidv
    ovnval2.3
    syl6eqr
    infeq1d
    ifbieq2d
    adantl
    wph
    cA
    @15
    wcel
    #
    cA
    @14
    wss
    #
    ovnval2.2
    wph
    cA
    cvv
    wcel
    @21
    @22
    wb
    wph
    cA
    @14
    cvv
    wph
    cr
    cX
    cmap
    ovexd
    ovnval2.2
    ssexd
    cA
    @14
    cvv
    elpwg
    syl
    mpbird
    wph
    @0
    cc0
    @12
    cvv
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    wph
    @12
    @20
    cxr
    clt
    cinf
    #
    cvv
    cxr
    cM
    @20
    clt
    ovnval2.3
    infeq1i
    @23
    cvv
    wcel
    wph
    cxr
    @20
    clt
    xrltso
    infex
    a1i
    syl5eqel
    ifcld
    fvmptd
end
