include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "cun.mm"
include "cfv.mm"
include "wceq.mm"
include "nosupno.mm"
include "bdayval.mm"
include "syl.mm"
include "nosupbday.mm"
include "eqsstr3d.mm"
include "adantr.mm"
include "unss1.mm"
include "simpll.mm"
include "simplr.mm"
include "simprr.mm"
include "noetalem1.mm"
include "syl3anc.mm"
include "cdif.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "dmeqi.mm"
include "dmun.mm"
include "c0.mm"
include "wne.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "snnz.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "uneq2i.mm"
include "undif2.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "imaundi.mm"
include "unieqi.mm"
include "uniun.mm"
include "suceq.mm"
include "word.mm"
include "crn.mm"
include "imassrn.mm"
include "wfo.mm"
include "bdayfo.mm"
include "forn.mm"
include "sseqtri.mm"
include "ssorduni.mm"
include "ordsucun.mm"
include "mp2an.mm"
include "a1i.mm"
include "3sstr4d.mm"

theorem noetalem4
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let cZ: class Z
  assume noetalem.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )
  assume noetalem.2: |- Z = ( S u. ( ( suc U. ( bday " B ) \ dom S ) X. { 1o } ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  assert |- ( ( ( A C_ No /\ A e. _V ) /\ ( B C_ No /\ B e. _V ) ) -> ( bday ` Z ) C_ suc U. ( bday " ( A u. B ) ) )

  proof
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cB
    csur
    wss
    #
    cB
    cvv
    wcel
    #
    wa
    #
    wa
    #
    cS
    cdm
    #
    cbday
    cB
    cima
    #
    cuni
    #
    csuc
    #
    cun
    #
    cbday
    cA
    cima
    #
    cuni
    #
    csuc
    #
    @10
    cun
    #
    cZ
    cbday
    cfv
    #
    cbday
    cA
    cB
    cun
    cima
    #
    cuni
    #
    csuc
    #
    @6
    @7
    @14
    wss
    #
    @11
    @15
    wss
    @2
    @20
    @5
    @2
    @7
    cS
    cbday
    cfv
    #
    @14
    @2
    cS
    csur
    wcel
    @21
    @7
    wceq
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    noetalem.1
    nosupno
    cS
    bdayval
    syl
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    noetalem.1
    nosupbday
    eqsstr3d
    adantr
    @7
    @14
    @10
    unss1
    syl
    @6
    @16
    cZ
    cdm
    #
    @11
    @6
    cZ
    csur
    wcel
    #
    @16
    @22
    wceq
    @6
    @0
    @1
    @4
    @23
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    @2
    @3
    @4
    simprr
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    vg
    cZ
    noetalem.1
    noetalem.2
    noetalem1
    syl3anc
    cZ
    bdayval
    syl
    @22
    cS
    @10
    @7
    cdif
    #
    c1o
    csn
    #
    cxp
    #
    cun
    #
    cdm
    #
    @11
    cZ
    @27
    noetalem.2
    dmeqi
    @28
    @7
    @26
    cdm
    #
    cun
    #
    @11
    cS
    @26
    dmun
    @30
    @7
    @24
    cun
    @11
    @29
    @24
    @7
    @25
    c0
    wne
    @29
    @24
    wceq
    c1o
    c1o
    con0
    1on
    elexi
    snnz
    @24
    @25
    dmxp
    ax-mp
    uneq2i
    @7
    @10
    undif2
    eqtri
    eqtri
    eqtri
    syl6eq
    @19
    @15
    wceq
    @6
    @19
    @13
    @9
    cun
    #
    csuc
    #
    @15
    @18
    @31
    wceq
    @19
    @32
    wceq
    @18
    @12
    @8
    cun
    #
    cuni
    @31
    @17
    @33
    cbday
    cA
    cB
    imaundi
    unieqi
    @12
    @8
    uniun
    eqtri
    @18
    @31
    suceq
    ax-mp
    @13
    word
    #
    @9
    word
    #
    @32
    @15
    wceq
    @12
    con0
    wss
    @34
    @12
    cbday
    crn
    #
    con0
    cbday
    cA
    imassrn
    csur
    con0
    cbday
    wfo
    @36
    con0
    wceq
    bdayfo
    csur
    con0
    cbday
    forn
    ax-mp
    #
    sseqtri
    @12
    ssorduni
    ax-mp
    @8
    con0
    wss
    @35
    @8
    @36
    con0
    cbday
    cB
    imassrn
    @37
    sseqtri
    @8
    ssorduni
    ax-mp
    @13
    @9
    ordsucun
    mp2an
    eqtri
    a1i
    3sstr4d
end
