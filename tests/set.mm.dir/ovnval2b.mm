include "covoln.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cn.mm"
include "cv.mm"
include "cico.mm"
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
include "eqid.mm"
include "ovnval2.mm"
include "biidd.mm"
include "cpw.mm"
include "cvv.mm"
include "a1i.mm"
include "cleq1lem.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "adantl.mm"
include "ovexd.mm"
include "ssexd.mm"
include "elpwd.mm"
include "wcel.mm"
include "xrex.mm"
include "rabex.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "eqtrd.mm"

theorem ovnval2b
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume ovnval2b.1: |- ( ph -> X e. Fin )
  assume ovnval2b.2: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnval2b.3: |- L = ( a e. ~P ( RR ^m X ) |-> { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( a C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) } )

  disjoint A a
  disjoint A i
  disjoint A z
  disjoint a i
  disjoint a z
  disjoint i z
  disjoint X a
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint a j
  disjoint a k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint a ph
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` A ) = if ( X = (/) , 0 , inf ( ( L ` A ) , RR* , < ) ) )

  proof
    wph
    cA
    cX
    covoln
    cfv
    cfv
    cX
    c0
    wceq
    #
    cc0
    cA
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
    vz
    cv
    vj
    cn
    cX
    @1
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
    @0
    cc0
    cA
    cL
    cfv
    #
    cxr
    clt
    cinf
    #
    cif
    wph
    vz
    cA
    vi
    vj
    vk
    @7
    cX
    ovnval2b.1
    ovnval2b.2
    @7
    eqid
    ovnval2
    wph
    @0
    @0
    @8
    @10
    cc0
    wph
    @0
    biidd
    wph
    cxr
    @7
    @9
    clt
    wph
    @9
    @7
    wph
    va
    cA
    va
    cv
    #
    @2
    wss
    @3
    wa
    #
    vi
    @5
    wrex
    #
    vz
    cxr
    crab
    #
    @7
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cL
    cvv
    cL
    va
    @16
    @14
    cmpt
    wceq
    wph
    ovnval2b.3
    a1i
    @11
    cA
    wceq
    #
    @14
    @7
    wceq
    wph
    @17
    @13
    @6
    vz
    cxr
    @17
    @12
    @4
    vi
    @5
    @3
    @11
    cA
    @2
    cleq1lem
    rexbidv
    rabbidv
    adantl
    wph
    cA
    @15
    cvv
    wph
    cA
    @15
    cvv
    wph
    cr
    cX
    cmap
    ovexd
    ovnval2b.2
    ssexd
    ovnval2b.2
    elpwd
    @7
    cvv
    wcel
    wph
    @6
    vz
    cxr
    xrex
    rabex
    a1i
    fvmptd
    eqcomd
    infeq1d
    ifbieq2d
    eqtrd
end
