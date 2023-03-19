include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "wa.mm"
include "fveq2.mm"
include "oveqd.mm"
include "adantl.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "wb.mm"
include "feq2.mm"
include "mpbid.mm"
include "hoidmv0val.mm"
include "eqtrd.mm"
include "wn.mm"
include "nfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "wne.mm"
include "neqne.mm"
include "n0.mm"
include "sylib.mm"
include "wi.mm"
include "simpr.mm"
include "ffvelrnda.mm"
include "eqidd.mm"
include "eqled.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "hoidmvval0.mm"
include "pm2.61dan.mm"

theorem hoidmvval0b
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  assume hoidmvval0b.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvval0b.x: |- ( ph -> X e. Fin )
  assume hoidmvval0b.a: |- ( ph -> A : X --> RR )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A j
  disjoint j k
  disjoint X j
  disjoint j ph
  assert |- ( ph -> ( A ( L ` X ) A ) = 0 )

  proof
    wph
    cX
    c0
    wceq
    #
    cA
    cA
    cX
    cL
    cfv
    #
    co
    #
    cc0
    wceq
    wph
    @0
    wa
    #
    @2
    cA
    cA
    c0
    cL
    cfv
    #
    co
    #
    cc0
    @0
    @2
    @5
    wceq
    wph
    @0
    @1
    @4
    cA
    cA
    cX
    c0
    cL
    fveq2
    oveqd
    adantl
    @3
    vx
    cA
    cA
    vk
    cL
    va
    vb
    hoidmvval0b.l
    @3
    cX
    cr
    cA
    wf
    #
    c0
    cr
    cA
    wf
    #
    wph
    @6
    @0
    hoidmvval0b.a
    adantr
    @0
    @6
    @7
    wb
    wph
    cX
    c0
    cr
    cA
    feq2
    adantl
    mpbid
    #
    @8
    hoidmv0val
    eqtrd
    wph
    @0
    wn
    #
    wa
    #
    vx
    cA
    cA
    vj
    vk
    cL
    cX
    va
    vb
    @10
    vj
    nfv
    hoidmvval0b.l
    wph
    cX
    cfn
    wcel
    @9
    hoidmvval0b.x
    adantr
    wph
    @6
    @9
    hoidmvval0b.a
    adantr
    #
    @11
    @10
    vj
    cv
    #
    cX
    wcel
    #
    @12
    cA
    cfv
    #
    @14
    cle
    wbr
    #
    wa
    #
    vj
    wex
    #
    @15
    vj
    cX
    wrex
    @10
    @13
    vj
    wex
    #
    @17
    @9
    @18
    wph
    @9
    cX
    c0
    wne
    @18
    cX
    c0
    neqne
    vj
    cX
    n0
    sylib
    adantl
    @10
    @13
    @16
    vj
    wph
    @13
    @16
    wi
    @9
    wph
    @13
    @16
    wph
    @13
    wa
    #
    @13
    @15
    wph
    @13
    simpr
    @19
    @14
    @14
    wph
    cX
    cr
    @12
    cA
    hoidmvval0b.a
    ffvelrnda
    @19
    @14
    eqidd
    eqled
    jca
    ex
    adantr
    eximdv
    mpd
    @15
    vj
    cX
    df-rex
    sylibr
    hoidmvval0
    pm2.61dan
end
