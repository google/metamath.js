include "cin.mm"
include "wcel.mm"
include "cfv.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cfn.mm"
include "cn.mm"
include "wss.mm"
include "cbits.mm"
include "cres.mm"
include "ccom.mm"
include "cind.mm"
include "eulerpartlemgv.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "cvv.mm"
include "wceq.mm"
include "nnex.mm"
include "crn.mm"
include "imassrn.mm"
include "cn0.mm"
include "cxp.mm"
include "wf1o.mm"
include "wf.mm"
include "oddpwdc.mm"
include "f1of.mm"
include "frn.mm"
include "mp2b.mm"
include "sstri.mm"
include "indpi1.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "wfun.mm"
include "ffun.mm"
include "cpw.mm"
include "inss2.mm"
include "eulerpartlemmf.mm"
include "eulerpartlem1.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "syl.mm"
include "sseldi.mm"
include "imafi.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "cc0.mm"
include "cdif.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "eulerpartgbij.mm"
include "elin.mm"
include "simplbi.mm"
include "elmapi.mm"
include "3syl.mm"
include "ssv.mm"
include "dfn2.mm"
include "ssdif.mm"
include "syl5eqss.mm"
include "sspreima.mm"
include "sylancl.mm"
include "csupp.mm"
include "fvex.mm"
include "0nn0.mm"
include "suppimacnv.mm"
include "wne.mm"
include "0ne1.mm"
include "difprsn1.mm"
include "eqcomi.mm"
include "ffs2.mm"
include "mp3an12.mm"
include "syl5eqr.mm"
include "sseqtrd.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem eulerpartlemgf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
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

  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f o
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g o
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k o
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint f r
  disjoint A f
  disjoint o r
  disjoint A o
  disjoint A r
  disjoint F o
  disjoint H o
  disjoint H r
  disjoint J f
  disjoint n r
  disjoint J n
  disjoint J o
  disjoint r x
  disjoint r y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint M o
  disjoint M r
  disjoint N f
  disjoint N g
  disjoint N x
  disjoint P g
  disjoint P n
  disjoint R f
  disjoint R o
  disjoint T f
  disjoint T o
  assert |- ( A e. ( T i^i R ) -> ( `' ( G ` A ) " NN ) e. Fin )

  proof
    cA
    cT
    cR
    cin
    #
    wcel
    #
    cA
    cG
    cfv
    #
    ccnv
    #
    c1
    csn
    #
    cima
    #
    cfn
    wcel
    @3
    cn
    cima
    #
    @5
    wss
    @6
    cfn
    wcel
    @1
    @5
    cF
    cbits
    cA
    cJ
    cres
    ccom
    #
    cM
    cfv
    #
    cima
    #
    cfn
    @1
    @5
    @9
    cn
    cind
    cfv
    cfv
    #
    ccnv
    #
    @4
    cima
    #
    @9
    @1
    @3
    @11
    @4
    @1
    @2
    @10
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
    vo
    cF
    cG
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
    eulerpart.g
    eulerpartlemgv
    cnveqd
    imaeq1d
    cn
    cvv
    wcel
    #
    @9
    cn
    wss
    @12
    @9
    wceq
    nnex
    @9
    cF
    crn
    #
    cn
    cF
    @8
    imassrn
    cJ
    cn0
    cxp
    #
    cn
    cF
    wf1o
    #
    @15
    cn
    cF
    wf
    #
    @14
    cn
    wss
    vx
    vy
    vz
    cF
    cJ
    eulerpart.j
    eulerpart.f
    oddpwdc
    #
    @15
    cn
    cF
    f1of
    #
    @15
    cn
    cF
    frn
    mp2b
    sstri
    @9
    cn
    cvv
    indpi1
    mp2an
    syl6eq
    @1
    cF
    wfun
    #
    @8
    cfn
    wcel
    @9
    cfn
    wcel
    @16
    @17
    @20
    @18
    @19
    @15
    cn
    cF
    ffun
    mp2b
    @1
    @15
    cpw
    #
    cfn
    cin
    #
    cfn
    @8
    @21
    cfn
    inss2
    @1
    @7
    cH
    wcel
    @8
    @22
    wcel
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
    vo
    cF
    cG
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
    eulerpart.g
    eulerpartlemmf
    cH
    @22
    @7
    cM
    cH
    @22
    cM
    wf1o
    cH
    @22
    cM
    wf
    vx
    vy
    vz
    cD
    cP
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
    eulerpartlem1
    cH
    @22
    cM
    f1of
    ax-mp
    ffvelrni
    syl
    sseldi
    cF
    @8
    imafi
    sylancr
    eqeltrd
    @1
    @6
    @3
    cvv
    cc0
    csn
    #
    cdif
    #
    cima
    #
    @5
    @1
    @2
    wfun
    #
    cn
    @24
    wss
    #
    @6
    @25
    wss
    @1
    cn
    cc0
    c1
    cpr
    #
    @2
    wf
    #
    @26
    @1
    @2
    @28
    cn
    cmap
    co
    #
    cR
    cin
    #
    wcel
    #
    @2
    @30
    wcel
    #
    @29
    @0
    @31
    cA
    cG
    @0
    @31
    cG
    wf1o
    @0
    @31
    cG
    wf
    vx
    vy
    vz
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
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
    eulerpart.g
    eulerpartgbij
    @0
    @31
    cG
    f1of
    ax-mp
    ffvelrni
    @32
    @33
    @2
    cR
    wcel
    @2
    @30
    cR
    elin
    simplbi
    @2
    @28
    cn
    elmapi
    3syl
    #
    cn
    @28
    @2
    ffun
    syl
    cn0
    cvv
    wss
    #
    @27
    cn0
    ssv
    @35
    cn
    cn0
    @23
    cdif
    @24
    dfn2
    cn0
    cvv
    @23
    ssdif
    syl5eqss
    ax-mp
    cn
    @24
    @2
    sspreima
    sylancl
    @1
    @25
    @2
    cc0
    csupp
    co
    #
    @5
    @2
    cvv
    wcel
    cc0
    cn0
    wcel
    #
    @36
    @25
    wceq
    cA
    cG
    fvex
    0nn0
    @2
    cvv
    cn0
    cc0
    suppimacnv
    mp2an
    @1
    @29
    @36
    @5
    wceq
    #
    @34
    @13
    @37
    @29
    @38
    nnex
    0nn0
    cn
    @28
    @4
    @2
    cvv
    cn0
    cc0
    @28
    @23
    cdif
    #
    @4
    cc0
    c1
    wne
    @39
    @4
    wceq
    0ne1
    cc0
    c1
    difprsn1
    ax-mp
    eqcomi
    ffs2
    mp3an12
    syl
    syl5eqr
    sseqtrd
    @5
    @6
    ssfi
    syl2anc
end
