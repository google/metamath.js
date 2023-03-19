include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cn.mm"
include "cdif.mm"
include "wa.mm"
include "cfv.mm"
include "wn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "eldif.mm"
include "breq2.mm"
include "notbid.mm"
include "elrab2.mm"
include "simplbi2.mm"
include "con1d.mm"
include "imp.mm"
include "sylbi.mm"
include "adantl.mm"
include "adantr.mm"
include "ccnv.mm"
include "cima.mm"
include "simpll.mm"
include "wb.mm"
include "eldifi.mm"
include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "wss.mm"
include "eulerpartlemt0.mm"
include "simp1bi.mm"
include "elmapi.mm"
include "syl.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "baibd.mm"
include "sylan2.mm"
include "biimpar.mm"
include "simp3bi.mm"
include "sselda.mm"
include "simprbi.mm"
include "syl2anc.mm"
include "pm2.65da.mm"
include "ffvelrnd.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"

theorem eulerpartlemf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
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
  disjoint N f
  disjoint P g
  assert |- ( ( A e. ( T i^i R ) /\ t e. ( NN \ J ) ) -> ( A ` t ) = 0 )

  proof
    cA
    cT
    cR
    cin
    wcel
    #
    vt
    cv
    #
    cn
    cJ
    cdif
    wcel
    #
    wa
    #
    @1
    cA
    cfv
    #
    cn
    wcel
    #
    wn
    @5
    @4
    cc0
    wceq
    #
    wo
    #
    @6
    @3
    @5
    c2
    @1
    cdvds
    wbr
    #
    @3
    @8
    @5
    @2
    @8
    @0
    @2
    @1
    cn
    wcel
    #
    @1
    cJ
    wcel
    #
    wn
    #
    wa
    @8
    @1
    cn
    cJ
    eldif
    @9
    @11
    @8
    @9
    @8
    @10
    @10
    @9
    @8
    wn
    #
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
    @1
    cn
    cJ
    @13
    @1
    wceq
    @14
    @8
    @13
    @1
    c2
    cdvds
    breq2
    notbid
    eulerpart.j
    elrab2
    #
    simplbi2
    con1d
    imp
    sylbi
    adantl
    adantr
    @3
    @5
    wa
    @0
    @1
    cA
    ccnv
    cn
    cima
    #
    wcel
    #
    @12
    @0
    @2
    @5
    simpll
    @3
    @17
    @5
    @2
    @0
    @9
    @17
    @5
    wb
    @1
    cn
    cJ
    eldifi
    #
    @0
    @17
    @9
    @5
    @0
    cn
    cn0
    cA
    wf
    #
    cA
    cn
    wfn
    @17
    @9
    @5
    wa
    wb
    @0
    cA
    cn0
    cn
    cmap
    co
    wcel
    #
    @19
    @0
    @20
    @16
    cfn
    wcel
    #
    @16
    cJ
    wss
    #
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
    #
    simp1bi
    cA
    cn0
    cn
    elmapi
    syl
    #
    cn
    cn0
    cA
    ffn
    cn
    @1
    cn
    cA
    elpreima
    3syl
    baibd
    sylan2
    biimpar
    @0
    @17
    wa
    @10
    @12
    @0
    @16
    cJ
    @1
    @0
    @20
    @21
    @22
    @23
    simp3bi
    sselda
    @10
    @9
    @12
    @15
    simprbi
    syl
    syl2anc
    pm2.65da
    @3
    @4
    cn0
    wcel
    @7
    @3
    cn
    cn0
    @1
    cA
    @0
    @19
    @2
    @24
    adantr
    @2
    @9
    @0
    @18
    adantl
    ffvelrnd
    @4
    elnn0
    sylib
    @5
    @6
    orel1
    sylc
end
