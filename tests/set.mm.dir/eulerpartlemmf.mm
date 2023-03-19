include "cin.mm"
include "wcel.mm"
include "cbits.mm"
include "cres.mm"
include "ccom.mm"
include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cmap.mm"
include "co.mm"
include "ccnv.mm"
include "cvv.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wf.mm"
include "wf1o.mm"
include "bitsf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "cn.mm"
include "wss.mm"
include "w3a.mm"
include "eulerpartlemt0.mm"
include "biimpi.mm"
include "simp1d.mm"
include "nn0ex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "fssres.mm"
include "sylancl.mm"
include "fco2.mm"
include "sylancr.mm"
include "pwex.mm"
include "inex1.mm"
include "ssexi.mm"
include "sylibr.mm"
include "cc0.mm"
include "simp2d.mm"
include "csupp.mm"
include "wceq.mm"
include "0nn0.mm"
include "suppimacnv.mm"
include "mpan2.mm"
include "wi.mm"
include "frnsuppeq.mm"
include "mp2an.mm"
include "syl.mm"
include "eqtr3d.mm"
include "eleq1d.mm"
include "dfn2.mm"
include "imaeq2i.mm"
include "eleq1i.mm"
include "syl6bbr.mm"
include "mpbird.mm"
include "resss.mm"
include "cnvss.mm"
include "imass1.mm"
include "mp2b.mm"
include "ssfi.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "wfun.mm"
include "ffun.mm"
include "funres.mm"
include "3syl.mm"
include "ssv.mm"
include "ssdif.mm"
include "cz.mm"
include "bitsf.mm"
include "difpreima.mm"
include "wf1.mm"
include "bitsf1.mm"
include "0z.mm"
include "snssi.mm"
include "f1imacnv.mm"
include "cfv.mm"
include "wfn.mm"
include "ffn.mm"
include "fnsnfv.mm"
include "0bits.mm"
include "sneqi.mm"
include "eqtr3i.mm"
include "difeq2i.mm"
include "3sstr4i.mm"
include "sspreima.mm"
include "syl5eqss.mm"
include "syl2anc.mm"
include "wa.mm"
include "oveq1.mm"
include "elrab2.mm"
include "wb.mm"
include "zex.mm"
include "fex.mm"
include "resexg.mm"
include "coexg.mm"
include "0ex.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "mpbir2and.mm"

theorem eulerpartlemmf
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
  let vt: setvar t
  let vw: setvar w
  let cB: class B
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
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint f o
  disjoint f r
  disjoint A f
  disjoint o r
  disjoint A o
  disjoint A r
  disjoint F o
  disjoint H r
  disjoint J f
  disjoint n o
  disjoint n r
  disjoint J n
  disjoint o x
  disjoint o y
  disjoint J o
  disjoint r x
  disjoint r y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint M o
  disjoint N f
  disjoint g n
  disjoint P g
  disjoint P n
  disjoint R o
  disjoint T o
  disjoint f t
  disjoint k t
  disjoint n t
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint f w
  disjoint o w
  disjoint r w
  disjoint A w
  disjoint B w
  disjoint F w
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint M w
  assert |- ( A e. ( T i^i R ) -> ( bits o. ( A |` J ) ) e. H )

  proof
    cA
    cT
    cR
    cin
    #
    wcel
    #
    cbits
    cA
    cJ
    cres
    #
    ccom
    #
    cH
    wcel
    #
    @3
    cn0
    cpw
    #
    cfn
    cin
    #
    cJ
    cmap
    co
    #
    wcel
    #
    @3
    ccnv
    #
    cvv
    c0
    csn
    #
    cdif
    #
    cima
    #
    cfn
    wcel
    #
    @1
    cJ
    @6
    @3
    wf
    #
    @8
    @1
    cn0
    @6
    cbits
    cn0
    cres
    #
    wf
    #
    cJ
    cn0
    @2
    wf
    #
    @14
    cn0
    @6
    @15
    wf1o
    @16
    bitsf1o
    cn0
    @6
    @15
    f1of
    ax-mp
    @1
    cn
    cn0
    cA
    wf
    #
    cJ
    cn
    wss
    @17
    @1
    cA
    cn0
    cn
    cmap
    co
    wcel
    #
    @18
    @1
    @19
    cA
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @21
    cJ
    wss
    #
    @1
    @19
    @22
    @23
    w3a
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
    biimpi
    #
    simp1d
    cn0
    cn
    cA
    nn0ex
    nnex
    elmap
    sylib
    #
    cJ
    c2
    vz
    cv
    cdvds
    wbr
    wn
    #
    vz
    cn
    crab
    cn
    eulerpart.j
    @26
    vz
    cn
    ssrab2
    eqsstri
    #
    cn
    cn0
    cJ
    cA
    fssres
    sylancl
    cJ
    cn0
    @6
    cbits
    @2
    fco2
    sylancr
    @6
    cJ
    @3
    @5
    cfn
    cn0
    nn0ex
    pwex
    inex1
    cJ
    cn
    nnex
    @27
    ssexi
    elmap
    sylibr
    @1
    @2
    ccnv
    #
    cvv
    cc0
    csn
    #
    cdif
    #
    cima
    #
    cfn
    wcel
    #
    @12
    @31
    wss
    @13
    @1
    @20
    @30
    cima
    #
    cfn
    wcel
    #
    @31
    @33
    wss
    #
    @32
    @1
    @34
    @22
    @1
    @19
    @22
    @23
    @24
    simp2d
    @1
    @34
    @20
    cn0
    @29
    cdif
    #
    cima
    #
    cfn
    wcel
    @22
    @1
    @33
    @37
    cfn
    @1
    cA
    cc0
    csupp
    co
    #
    @33
    @37
    @1
    cc0
    cn0
    wcel
    #
    @38
    @33
    wceq
    0nn0
    cA
    @0
    cn0
    cc0
    suppimacnv
    mpan2
    @1
    @18
    @38
    @37
    wceq
    #
    @25
    cn
    cvv
    wcel
    @39
    @18
    @40
    wi
    nnex
    0nn0
    cn0
    cA
    cn
    cvv
    cn0
    cc0
    frnsuppeq
    mp2an
    syl
    eqtr3d
    eleq1d
    @21
    @37
    cfn
    cn
    @36
    @20
    dfn2
    imaeq2i
    eleq1i
    syl6bbr
    mpbird
    @2
    cA
    wss
    @28
    @20
    wss
    @35
    cA
    cJ
    resss
    @2
    cA
    cnvss
    @28
    @20
    @30
    imass1
    mp2b
    @33
    @31
    ssfi
    sylancl
    @1
    @12
    @28
    cbits
    ccnv
    #
    @11
    cima
    #
    cima
    #
    @31
    @12
    @28
    @41
    ccom
    #
    @11
    cima
    @43
    @9
    @44
    @11
    cbits
    @2
    cnvco
    imaeq1i
    @28
    @41
    @11
    imaco
    eqtri
    @1
    @2
    wfun
    #
    @42
    @30
    wss
    @43
    @31
    wss
    @1
    @18
    cA
    wfun
    @45
    @25
    cn
    cn0
    cA
    ffun
    cJ
    cA
    funres
    3syl
    @41
    cvv
    cima
    #
    @41
    @10
    cima
    #
    cdif
    #
    cvv
    @47
    cdif
    #
    @42
    @30
    @46
    cvv
    wss
    @48
    @49
    wss
    @46
    ssv
    @46
    cvv
    @47
    ssdif
    ax-mp
    cz
    @5
    cbits
    wf
    #
    cbits
    wfun
    @42
    @48
    wceq
    bitsf
    cz
    @5
    cbits
    ffun
    cvv
    @10
    cbits
    difpreima
    mp2b
    @29
    @47
    cvv
    @41
    cbits
    @29
    cima
    #
    cima
    #
    @29
    @47
    cz
    @5
    cbits
    wf1
    @29
    cz
    wss
    #
    @52
    @29
    wceq
    bitsf1
    cc0
    cz
    wcel
    #
    @53
    0z
    cc0
    cz
    snssi
    ax-mp
    cz
    @5
    @29
    cbits
    f1imacnv
    mp2an
    @51
    @10
    @41
    cc0
    cbits
    cfv
    #
    csn
    #
    @51
    @10
    cbits
    cz
    wfn
    #
    @54
    @56
    @51
    wceq
    @50
    @57
    bitsf
    cz
    @5
    cbits
    ffn
    ax-mp
    0z
    cz
    cc0
    cbits
    fnsnfv
    mp2an
    @55
    c0
    0bits
    sneqi
    eqtr3i
    imaeq2i
    eqtr3i
    difeq2i
    3sstr4i
    @42
    @30
    @2
    sspreima
    sylancl
    syl5eqss
    @31
    @12
    ssfi
    syl2anc
    @4
    @8
    @3
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    wa
    #
    @1
    @8
    @13
    wa
    #
    vr
    cv
    #
    c0
    csupp
    co
    #
    cfn
    wcel
    @59
    vr
    @3
    @7
    cH
    @62
    @3
    wceq
    @63
    @58
    cfn
    @62
    @3
    c0
    csupp
    oveq1
    eleq1d
    eulerpart.h
    elrab2
    @1
    @3
    cvv
    wcel
    #
    @60
    @61
    wb
    @1
    cbits
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @64
    @50
    cz
    cvv
    wcel
    @65
    bitsf
    zex
    cz
    @5
    cvv
    cbits
    fex
    mp2an
    cA
    cJ
    @0
    resexg
    cbits
    @2
    cvv
    cvv
    coexg
    sylancr
    @64
    @59
    @13
    @8
    @64
    @58
    @12
    cfn
    @64
    c0
    cvv
    wcel
    @58
    @12
    wceq
    0ex
    @3
    cvv
    cvv
    c0
    suppimacnv
    mpan2
    eleq1d
    anbi2d
    syl
    syl5bb
    mpbir2and
end
