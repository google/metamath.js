include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "cima.mm"
include "cc0.mm"
include "cpr.mm"
include "wss.mm"
include "wceq.mm"
include "fveq1.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "cfz.mm"
include "co.mm"
include "c2.mm"
include "cfzo.mm"
include "cmin.mm"
include "cz.mm"
include "2z.mm"
include "fzoval.mm"
include "ax-mp.mm"
include "fzo0to2pr.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"
include "eleq2i.mm"
include "cn0.mm"
include "wb.mm"
include "wf.mm"
include "ccnv.mm"
include "cfn.mm"
include "cmul.mm"
include "csu.mm"
include "eulerpartleme.mm"
include "simp1bi.mm"
include "ffvelrnda.mm"
include "1nn0.mm"
include "w3a.mm"
include "elfz2nn0.mm"
include "df-3an.mm"
include "bitri.mm"
include "baib.mm"
include "sylancl.mm"
include "syl5rbb.mm"
include "ralbidva.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "syl.mm"
include "fdm.mm"
include "eqimss2.mm"
include "3syl.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "pm5.32i.mm"

theorem eulerpartlemd
  let cA: class A
  let cD: class D
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let cO: class O
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }

  disjoint f g
  disjoint f k
  disjoint f n
  disjoint A f
  disjoint g k
  disjoint g n
  disjoint A g
  disjoint k n
  disjoint A k
  disjoint A n
  disjoint N f
  disjoint P g
  disjoint P n
  assert |- ( A e. D <-> ( A e. P /\ ( A " NN ) C_ { 0 , 1 } ) )

  proof
    cA
    cD
    wcel
    cA
    cP
    wcel
    #
    vn
    cv
    #
    cA
    cfv
    #
    c1
    cle
    wbr
    #
    vn
    cn
    wral
    #
    wa
    @0
    cA
    cn
    cima
    cc0
    c1
    cpr
    #
    wss
    #
    wa
    @1
    vg
    cv
    #
    cfv
    #
    c1
    cle
    wbr
    #
    vn
    cn
    wral
    @4
    vg
    cA
    cP
    cD
    @7
    cA
    wceq
    #
    @9
    @3
    vn
    cn
    @10
    @8
    @2
    c1
    cle
    @1
    @7
    cA
    fveq1
    breq1d
    ralbidv
    eulerpart.d
    elrab2
    @0
    @4
    @6
    @0
    @4
    @2
    @5
    wcel
    #
    vn
    cn
    wral
    #
    @6
    @0
    @3
    @11
    vn
    cn
    @11
    @2
    cc0
    c1
    cfz
    co
    #
    wcel
    #
    @0
    @1
    cn
    wcel
    wa
    #
    @3
    @5
    @13
    @2
    cc0
    c2
    cfzo
    co
    #
    cc0
    c2
    c1
    cmin
    co
    #
    cfz
    co
    #
    @5
    @13
    c2
    cz
    wcel
    @16
    @18
    wceq
    2z
    cc0
    c2
    fzoval
    ax-mp
    fzo0to2pr
    @17
    c1
    cc0
    cfz
    2m1e1
    oveq2i
    3eqtr3i
    eleq2i
    @15
    @2
    cn0
    wcel
    #
    c1
    cn0
    wcel
    #
    @14
    @3
    wb
    @0
    cn
    cn0
    @1
    cA
    @0
    cn
    cn0
    cA
    wf
    #
    cA
    ccnv
    cn
    cima
    cfn
    wcel
    cn
    vk
    cv
    #
    cA
    cfv
    @22
    cmul
    co
    vk
    csu
    cN
    wceq
    cA
    cP
    vf
    vk
    cN
    eulerpart.p
    eulerpartleme
    simp1bi
    #
    ffvelrnda
    1nn0
    @14
    @19
    @20
    wa
    #
    @3
    @14
    @19
    @20
    @3
    w3a
    @24
    @3
    wa
    @2
    c1
    elfz2nn0
    @19
    @20
    @3
    df-3an
    bitri
    baib
    sylancl
    syl5rbb
    ralbidva
    @0
    cA
    wfun
    #
    cn
    cA
    cdm
    #
    wss
    #
    @6
    @12
    wb
    @0
    @21
    @25
    @23
    cn
    cn0
    cA
    ffun
    syl
    @0
    @21
    @26
    cn
    wceq
    @27
    @23
    cn
    cn0
    cA
    fdm
    cn
    @26
    eqimss2
    3syl
    vn
    cn
    @5
    cA
    funimass4
    syl2anc
    bitr4d
    pm5.32i
    bitri
end
