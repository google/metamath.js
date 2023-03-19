include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "id.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "fveq2.mm"
include "breq12d.mm"
include "cbvrexv.mm"
include "rexn0.mm"
include "sylbir.mm"
include "syl.mm"
include "wa.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cfn.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "cr.mm"
include "wf.mm"
include "hoidmvn0val.mm"
include "nfv.mm"
include "nfan.mm"
include "w3a.mm"
include "nfcv.mm"
include "3ad2ant1.mm"
include "cc.mm"
include "ffvelrnda.mm"
include "volicore.mm"
include "syl2anc.mm"
include "recnd.mm"
include "3ad2antl1.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "simp2.mm"
include "clt.mm"
include "cmin.mm"
include "cif.mm"
include "3adant3.mm"
include "volico.mm"
include "wn.mm"
include "simp3.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "fprod0.mm"
include "3adant1r.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "eqidd.mm"
include "3eqtrd.mm"

theorem hoidmvval0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume hoidmvval0.p: |- F/ j ph
  assume hoidmvval0.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvval0.x: |- ( ph -> X e. Fin )
  assume hoidmvval0.a: |- ( ph -> A : X --> RR )
  assume hoidmvval0.b: |- ( ph -> B : X --> RR )
  assume hoidmvval0.j: |- ( ph -> E. j e. X ( B ` j ) <_ ( A ` j ) )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint A j
  disjoint j k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint B j
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint X j
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( A ( L ` X ) B ) = 0 )

  proof
    wph
    wph
    cX
    c0
    wne
    #
    cA
    cB
    cX
    cL
    cfv
    co
    #
    cc0
    wceq
    wph
    id
    wph
    vj
    cv
    #
    cB
    cfv
    #
    @2
    cA
    cfv
    #
    cle
    wbr
    #
    vj
    cX
    wrex
    #
    @0
    hoidmvval0.j
    @6
    vk
    cv
    #
    cB
    cfv
    #
    @7
    cA
    cfv
    #
    cle
    wbr
    #
    vk
    cX
    wrex
    @0
    @10
    @5
    vk
    vj
    cX
    @7
    @2
    wceq
    #
    @8
    @3
    @9
    @4
    cle
    @7
    @2
    cB
    fveq2
    #
    @7
    @2
    cA
    fveq2
    #
    breq12d
    cbvrexv
    @10
    vk
    cX
    rexn0
    sylbir
    syl
    wph
    @0
    wa
    #
    @1
    cX
    @9
    @8
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cc0
    cc0
    @14
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hoidmvval0.l
    wph
    cX
    cfn
    wcel
    #
    @0
    hoidmvval0.x
    adantr
    wph
    @0
    simpr
    wph
    cX
    cr
    cA
    wf
    @0
    hoidmvval0.a
    adantr
    wph
    cX
    cr
    cB
    wf
    @0
    hoidmvval0.b
    adantr
    hoidmvn0val
    @14
    @6
    @17
    cc0
    wceq
    #
    wph
    @6
    @0
    hoidmvval0.j
    adantr
    @14
    @5
    @19
    vj
    cX
    wph
    @0
    vj
    hoidmvval0.p
    @0
    vj
    nfv
    nfan
    @19
    vj
    nfv
    @14
    @2
    cX
    wcel
    #
    @5
    @19
    wph
    @20
    @5
    @19
    @0
    wph
    @20
    @5
    w3a
    #
    cX
    @16
    @4
    @3
    cico
    co
    #
    cvol
    cfv
    #
    vk
    @2
    @21
    vk
    nfv
    vk
    @23
    nfcv
    wph
    @20
    @18
    @5
    hoidmvval0.x
    3ad2ant1
    wph
    @20
    @7
    cX
    wcel
    #
    @16
    cc
    wcel
    @5
    wph
    @24
    wa
    #
    @16
    @25
    @9
    cr
    wcel
    @8
    cr
    wcel
    @16
    cr
    wcel
    wph
    cX
    cr
    @7
    cA
    hoidmvval0.a
    ffvelrnda
    wph
    cX
    cr
    @7
    cB
    hoidmvval0.b
    ffvelrnda
    @9
    @8
    volicore
    syl2anc
    recnd
    3ad2antl1
    @11
    @15
    @22
    cvol
    @11
    @9
    @4
    @8
    @3
    cico
    @13
    @12
    oveq12d
    fveq2d
    wph
    @20
    @5
    simp2
    @21
    @23
    @4
    @3
    clt
    wbr
    #
    @3
    @4
    cmin
    co
    #
    cc0
    cif
    #
    cc0
    @21
    @4
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @23
    @28
    wceq
    wph
    @20
    @29
    @5
    wph
    cX
    cr
    @2
    cA
    hoidmvval0.a
    ffvelrnda
    3adant3
    #
    wph
    @20
    @30
    @5
    wph
    cX
    cr
    @2
    cB
    hoidmvval0.b
    ffvelrnda
    3adant3
    #
    @4
    @3
    volico
    syl2anc
    @21
    @26
    @27
    cc0
    @21
    @5
    @26
    wn
    wph
    @20
    @5
    simp3
    @21
    @3
    @4
    @32
    @31
    lenltd
    mpbid
    iffalsed
    eqtrd
    fprod0
    3adant1r
    3exp
    rexlimd
    mpd
    @14
    cc0
    eqidd
    3eqtrd
    syl2anc
end
