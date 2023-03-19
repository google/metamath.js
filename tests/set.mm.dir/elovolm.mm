include "wcel.mm"
include "cxr.mm"
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
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "wf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "eqid.mm"
include "ovolsf.mm"
include "sylbi.mm"
include "icossxr.mm"
include "fss.mm"
include "sylancl.mm"
include "frn.mm"
include "supxrcl.mm"
include "3syl.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "adantrl.mm"
include "rexlimiva.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"

theorem elovolm
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
  assert |- ( B e. M <-> E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ B = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) )

  proof
    cB
    cM
    wcel
    cB
    cxr
    wcel
    #
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
    @1
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
    #
    wa
    @12
    @2
    vy
    cv
    #
    @6
    wceq
    #
    wa
    #
    vf
    @11
    wrex
    @12
    vy
    cB
    cxr
    cM
    @13
    cB
    wceq
    #
    @15
    @8
    vf
    @11
    @16
    @14
    @7
    @2
    @13
    cB
    @6
    eqeq1
    anbi2d
    rexbidv
    ovolval.1
    elrab2
    @12
    @0
    @8
    @0
    vf
    @11
    @1
    @11
    wcel
    #
    @7
    @0
    @2
    @17
    @7
    @0
    @17
    @0
    @7
    @6
    cxr
    wcel
    #
    @17
    cn
    cxr
    @4
    wf
    #
    @5
    cxr
    wss
    @18
    @17
    cn
    cc0
    cpnf
    cico
    co
    #
    @4
    wf
    #
    @20
    cxr
    wss
    @19
    @17
    cn
    @10
    @1
    wf
    @21
    @10
    cn
    @1
    @9
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    @4
    @1
    @3
    @3
    eqid
    @4
    eqid
    ovolsf
    sylbi
    cc0
    cpnf
    icossxr
    cn
    @20
    cxr
    @4
    fss
    sylancl
    cn
    cxr
    @4
    frn
    @5
    supxrcl
    3syl
    cB
    @6
    cxr
    eleq1
    syl5ibrcom
    imp
    adantrl
    rexlimiva
    pm4.71ri
    bitr4i
end
