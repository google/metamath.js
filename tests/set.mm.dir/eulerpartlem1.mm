include "cn0.mm"
include "cxp.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "cres.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cn.mm"
include "nnex.mm"
include "rabex2.mm"
include "nn0ex.mm"
include "eqid.mm"
include "fpwrelmapffs.mm"
include "wceq.mm"
include "wb.mm"
include "wss.mm"
include "c0.mm"
include "csupp.mm"
include "crab.mm"
include "ssrab2.mm"
include "cvv.mm"
include "pwex.mm"
include "inss1.mm"
include "mapss.mm"
include "mp2an.mm"
include "sstri.mm"
include "eqsstri.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "f1oeq1.mm"
include "mpbir.mm"

theorem eulerpartlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cP: class P
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

  disjoint r x
  disjoint r y
  disjoint J r
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint H r
  assert |- M : H -1-1-onto-> ( ~P ( J X. NN0 ) i^i Fin )

  proof
    cH
    cJ
    cn0
    cxp
    cpw
    cfn
    cin
    #
    cM
    wf1o
    #
    cH
    @0
    vr
    cn0
    cpw
    #
    cJ
    cmap
    co
    #
    vx
    cv
    #
    cJ
    wcel
    vy
    cv
    @4
    vr
    cv
    #
    cfv
    wcel
    wa
    vx
    vy
    copab
    #
    cmpt
    #
    cH
    cres
    #
    wf1o
    #
    vx
    vy
    cJ
    cn0
    cH
    vr
    @7
    c2
    vz
    cv
    cdvds
    wbr
    wn
    vz
    cn
    cJ
    eulerpart.j
    nnex
    rabex2
    nn0ex
    @7
    eqid
    eulerpart.h
    fpwrelmapffs
    cM
    @8
    wceq
    @1
    @9
    wb
    cM
    vr
    cH
    @6
    cmpt
    #
    @8
    eulerpart.m
    cH
    @3
    wss
    @8
    @10
    wceq
    cH
    @5
    c0
    csupp
    co
    cfn
    wcel
    #
    vr
    @2
    cfn
    cin
    #
    cJ
    cmap
    co
    #
    crab
    #
    @3
    eulerpart.h
    @14
    @13
    @3
    @11
    vr
    @13
    ssrab2
    @2
    cvv
    wcel
    @12
    @2
    wss
    @13
    @3
    wss
    cn0
    nn0ex
    pwex
    @2
    cfn
    inss1
    @12
    @2
    cJ
    cvv
    mapss
    mp2an
    sstri
    eqsstri
    vr
    @3
    cH
    @6
    resmpt
    ax-mp
    eqtr4i
    cH
    @0
    cM
    @8
    f1oeq1
    ax-mp
    mpbir
end
