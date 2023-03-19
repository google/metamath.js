include "cin.mm"
include "wcel.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cbits.mm"
include "cxp.mm"
include "ciun.mm"
include "ccom.mm"
include "wa.mm"
include "copab.mm"
include "eqid.mm"
include "marypha2lem2.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "cn0.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "wss.mm"
include "eulerpartlemt0.mm"
include "simp1bi.mm"
include "elmapi.mm"
include "syl.mm"
include "adantr.mm"
include "ffun.mm"
include "inss1.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "syl5ss.mm"
include "sselda.mm"
include "wb.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "fvco.mm"
include "syl2anc.mm"
include "xpeq2d.mm"
include "iuneq2dv.mm"
include "syl5reqr.mm"
include "syl5eq.mm"

theorem eulerpartlemgu
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
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
  assume eulerpartlemgh.1: |- U = U_ t e. ( ( `' A " NN ) i^i J ) ( { t } X. ( bits ` ( A ` t ) ) )

  disjoint t z
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint A f
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint A g
  disjoint k n
  disjoint k t
  disjoint A k
  disjoint n t
  disjoint A n
  disjoint A t
  disjoint J f
  disjoint J n
  disjoint J t
  disjoint N f
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint O n
  disjoint O t
  disjoint P g
  disjoint P k
  disjoint R f
  disjoint R k
  disjoint R n
  disjoint R t
  disjoint T n
  disjoint T t
  assert |- ( A e. ( T i^i R ) -> U = { <. t , n >. | ( t e. ( ( `' A " NN ) i^i J ) /\ n e. ( ( bits o. A ) ` t ) ) } )

  proof
    cA
    cT
    cR
    cin
    wcel
    #
    cU
    vt
    cA
    ccnv
    cn
    cima
    #
    cJ
    cin
    #
    vt
    cv
    #
    csn
    #
    @3
    cA
    cfv
    cbits
    cfv
    #
    cxp
    #
    ciun
    #
    @3
    @2
    wcel
    #
    vn
    cv
    @3
    cbits
    cA
    ccom
    #
    cfv
    #
    wcel
    wa
    vt
    vn
    copab
    #
    eulerpartlemgh.1
    @0
    @11
    vt
    @2
    @4
    @10
    cxp
    #
    ciun
    #
    @7
    vt
    vn
    @2
    @13
    @9
    @13
    eqid
    marypha2lem2
    @0
    vt
    @2
    @12
    @6
    @0
    @8
    wa
    #
    @10
    @5
    @4
    @14
    cA
    wfun
    #
    @3
    cA
    cdm
    #
    wcel
    #
    @10
    @5
    wceq
    @14
    cn
    cn0
    cA
    wf
    #
    @15
    @0
    @18
    @8
    @0
    cA
    cn0
    cn
    cmap
    co
    wcel
    #
    @18
    @0
    @19
    @1
    cfn
    wcel
    @1
    cJ
    wss
    vx
    vy
    vz
    cA
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    simp1bi
    cA
    cn0
    cn
    elmapi
    syl
    #
    adantr
    cn
    cn0
    cA
    ffun
    syl
    @14
    @17
    @3
    cn
    wcel
    #
    @0
    @2
    cn
    @3
    @0
    @2
    @1
    cn
    @1
    cJ
    inss1
    @0
    @16
    @1
    cn
    cA
    cn
    cnvimass
    @0
    @18
    @16
    cn
    wceq
    @20
    cn
    cn0
    cA
    fdm
    syl
    #
    syl5sseq
    syl5ss
    sselda
    @0
    @17
    @21
    wb
    @8
    @0
    @16
    cn
    @3
    @22
    eleq2d
    adantr
    mpbird
    @3
    cbits
    cA
    fvco
    syl2anc
    xpeq2d
    iuneq2dv
    syl5reqr
    syl5eq
end
