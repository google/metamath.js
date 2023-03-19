include "wcel.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cc0.mm"
include "wbr.mm"
include "elovolm.mm"
include "wf.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "cfv.mm"
include "cpnf.mm"
include "cico.mm"
include "eqid.mm"
include "ovolsf.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "elrege0.mm"
include "simprbi.mm"
include "syl.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "wi.mm"
include "sseldi.mm"
include "supxrcl.mm"
include "0xr.mm"
include "xrletr.mm"
include "mp3an1.mm"
include "mp2and.mm"
include "sylbi.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "adantld.mm"
include "rexlimiv.mm"

theorem ovolmge0
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cM: class M
  let vx: setvar x
  let cF: class F
  let cS: class S
  assume ovolval.1: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }

  disjoint f y
  disjoint A f
  disjoint A y
  disjoint B f
  disjoint B y
  disjoint f x
  disjoint x y
  disjoint A x
  disjoint F f
  disjoint M x
  disjoint S f
  disjoint S y
  assert |- ( B e. M -> 0 <_ B )

  proof
    cB
    cM
    wcel
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    cB
    caddc
    cabs
    cmin
    ccom
    @0
    ccom
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    wrex
    cc0
    cB
    cle
    wbr
    #
    vy
    cA
    cB
    vf
    cM
    ovolval.1
    elovolm
    @7
    @11
    vf
    @10
    @0
    @10
    wcel
    #
    @6
    @11
    @1
    @12
    @11
    @6
    cc0
    @5
    cle
    wbr
    #
    @12
    cn
    @9
    @0
    wf
    #
    @13
    @9
    cn
    @0
    @8
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    @14
    cc0
    c1
    @3
    cfv
    #
    cle
    wbr
    #
    @15
    @5
    cle
    wbr
    #
    @13
    @14
    @15
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @16
    @14
    cn
    @18
    @3
    wf
    #
    c1
    cn
    wcel
    #
    @19
    @3
    @0
    @2
    @2
    eqid
    @3
    eqid
    ovolsf
    #
    1nn
    cn
    @18
    c1
    @3
    ffvelrn
    sylancl
    #
    @19
    @15
    cr
    wcel
    @16
    @15
    elrege0
    simprbi
    syl
    @14
    @4
    cxr
    wss
    #
    @15
    @4
    wcel
    #
    @17
    @14
    @4
    @18
    cxr
    @14
    @20
    @4
    @18
    wss
    @22
    cn
    @18
    @3
    frn
    syl
    cc0
    cpnf
    icossxr
    #
    syl6ss
    #
    @14
    @3
    cn
    wfn
    #
    @21
    @25
    @14
    @20
    @28
    @22
    cn
    @18
    @3
    ffn
    syl
    1nn
    cn
    c1
    @3
    fnfvelrn
    sylancl
    @4
    @15
    supxrub
    syl2anc
    @14
    @15
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @16
    @17
    wa
    @13
    wi
    #
    @14
    @18
    cxr
    @15
    @26
    @23
    sseldi
    @14
    @24
    @30
    @27
    @4
    supxrcl
    syl
    cc0
    cxr
    wcel
    @29
    @30
    @31
    0xr
    cc0
    @15
    @5
    xrletr
    mp3an1
    syl2anc
    mp2and
    sylbi
    cB
    @5
    cc0
    cle
    breq2
    syl5ibrcom
    adantld
    rexlimiv
    sylbi
end
