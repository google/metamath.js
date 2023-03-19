include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "anbi1i.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "wral.mm"
include "eulerpartlemo.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "cfn.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "weq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "nn0ex.mm"
include "nnex.mm"
include "elmap.mm"
include "fdm.mm"
include "sylbi.mm"
include "syl5sseq.mm"
include "syl.mm"
include "sselda.mm"
include "ralrimiva.mm"
include "biantrurd.mm"
include "simprbi.mm"
include "simpld.mm"
include "biantrud.mm"
include "3bitrd.mm"
include "dfss3.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbii.mm"
include "r19.26.mm"
include "3bitri.mm"
include "anbi2i.mm"
include "syl6bbr.mm"
include "sseq1d.mm"
include "vex.mm"
include "elab2.mm"
include "anbi12i.mm"
include "pm5.32i.mm"
include "ancom.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem eulerpartlemr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  let vh: setvar h
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )
  assume eulerpart.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpart.t: |- T = { f e. ( NN0 ^m NN ) | ( `' f " NN ) C_ J }
  assume eulerpart.g: |- G = ( o e. ( T i^i R ) |-> ( ( _Ind ` NN ) ` ( F " ( M ` ( bits o. ( o |` J ) ) ) ) ) )

  disjoint f k
  disjoint f n
  disjoint f z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint J f
  disjoint J n
  disjoint N f
  disjoint g n
  disjoint P g
  disjoint P n
  disjoint f h
  disjoint h k
  disjoint h n
  disjoint h z
  disjoint g h
  disjoint P h
  disjoint O h
  disjoint R h
  disjoint T h
  assert |- O = ( ( T i^i R ) i^i P )

  proof
    vh
    cO
    cT
    cR
    cin
    #
    cP
    cin
    #
    vh
    cv
    #
    @0
    wcel
    #
    @2
    cP
    wcel
    #
    wa
    @2
    cT
    wcel
    #
    @2
    cR
    wcel
    #
    wa
    #
    @4
    wa
    #
    @2
    @1
    wcel
    @2
    cO
    wcel
    #
    @3
    @7
    @4
    @2
    cT
    cR
    elin
    anbi1i
    @2
    @0
    cP
    elin
    @9
    @4
    c2
    vn
    cv
    #
    cdvds
    wbr
    #
    wn
    #
    vn
    @2
    ccnv
    #
    cn
    cima
    #
    wral
    #
    wa
    @4
    @7
    wa
    @8
    @2
    cD
    cP
    vf
    vg
    vk
    vn
    cN
    cO
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpartlemo
    @4
    @15
    @7
    @4
    @15
    @2
    cn0
    cn
    cmap
    co
    #
    wcel
    #
    @14
    cJ
    wss
    #
    wa
    #
    @14
    cfn
    wcel
    #
    wa
    #
    @7
    @4
    @15
    @17
    @10
    cn
    wcel
    #
    vn
    @14
    wral
    #
    @15
    wa
    #
    wa
    #
    @20
    wa
    #
    @21
    @4
    @15
    @24
    @25
    @26
    @4
    @23
    @15
    @4
    @22
    vn
    @14
    @4
    @14
    cn
    @10
    @4
    @17
    @14
    cn
    wss
    @4
    @17
    @20
    cn
    vk
    cv
    #
    @2
    cfv
    #
    @27
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    wa
    #
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    cn
    @27
    @33
    cfv
    #
    @27
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    wa
    @32
    vf
    @2
    @16
    cP
    vf
    vh
    weq
    #
    @36
    @20
    @40
    @31
    @41
    @35
    @14
    cfn
    @41
    @34
    @13
    cn
    @33
    @2
    cnveq
    imaeq1d
    #
    eleq1d
    #
    @41
    @39
    @30
    cN
    @41
    cn
    @38
    @29
    vk
    @41
    @37
    @28
    @27
    cmul
    @27
    @33
    @2
    fveq1
    oveq1d
    sumeq2sdv
    eqeq1d
    anbi12d
    eulerpart.p
    elrab2
    #
    simplbi
    #
    @17
    @2
    cdm
    #
    @14
    cn
    @2
    cn
    cnvimass
    @17
    cn
    cn0
    @2
    wf
    @46
    cn
    wceq
    cn0
    cn
    @2
    nn0ex
    nnex
    elmap
    cn
    cn0
    @2
    fdm
    sylbi
    syl5sseq
    syl
    sselda
    ralrimiva
    biantrurd
    @4
    @17
    @24
    @45
    biantrurd
    @4
    @20
    @25
    @4
    @20
    @31
    @4
    @17
    @32
    @44
    simprbi
    simpld
    biantrud
    3bitrd
    @19
    @25
    @20
    @18
    @24
    @17
    @18
    @10
    cJ
    wcel
    #
    vn
    @14
    wral
    @22
    @12
    wa
    #
    vn
    @14
    wral
    @24
    vn
    @14
    cJ
    dfss3
    @47
    @48
    vn
    @14
    c2
    vz
    cv
    #
    cdvds
    wbr
    #
    wn
    @12
    vz
    @10
    cn
    cJ
    vz
    vn
    weq
    @50
    @11
    @49
    @10
    c2
    cdvds
    breq2
    notbid
    eulerpart.j
    elrab2
    ralbii
    @22
    @12
    vn
    @14
    r19.26
    3bitri
    anbi2i
    anbi1i
    syl6bbr
    @5
    @19
    @6
    @20
    @35
    cJ
    wss
    @18
    vf
    @2
    @16
    cT
    @41
    @35
    @14
    cJ
    @42
    sseq1d
    eulerpart.t
    elrab2
    @36
    @20
    vf
    @2
    cR
    vh
    vex
    @43
    eulerpart.r
    elab2
    anbi12i
    syl6bbr
    pm5.32i
    @4
    @7
    ancom
    3bitri
    3bitr4ri
    eqriv
end
