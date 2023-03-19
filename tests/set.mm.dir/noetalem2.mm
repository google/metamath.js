include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "cres.mm"
include "cslt.mm"
include "wbr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "nosupbnd1.mm"
include "syl3anc.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "cdif.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "reseq1i.mm"
include "c0.mm"
include "resundir.mm"
include "cin.mm"
include "df-res.mm"
include "wceq.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "xpdisj1.mm"
include "ax-mp.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "wfun.mm"
include "wrel.mm"
include "nosupno.mm"
include "syl2anc.mm"
include "nofun.mm"
include "syl.mm"
include "funrel.mm"
include "resdm.mm"
include "3syl.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "con0.mm"
include "wi.mm"
include "simp1.mm"
include "sselda.mm"
include "noetalem1.mm"
include "adantr.mm"
include "nodmon.mm"
include "sltres.mm"
include "mpd.mm"

theorem noetalem2
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let cX: class X
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
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint x y
  disjoint X y
  assert |- ( ( ( A C_ No /\ A e. _V /\ B e. _V ) /\ X e. A ) -> X <s Z )

  proof
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    w3a
    #
    cX
    cA
    wcel
    #
    wa
    #
    cX
    cS
    cdm
    #
    cres
    #
    cZ
    @6
    cres
    #
    cslt
    wbr
    #
    cX
    cZ
    cslt
    wbr
    #
    @5
    @7
    cS
    @8
    cslt
    @5
    @0
    @1
    @4
    @7
    cS
    cslt
    wbr
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    @3
    @4
    simpr
    vx
    vy
    vv
    vu
    cA
    cS
    cX
    vg
    noetalem.1
    nosupbnd1
    syl3anc
    @5
    @8
    cS
    @6
    cres
    #
    cS
    @8
    cS
    cbday
    cB
    cima
    cuni
    csuc
    #
    @6
    cdif
    #
    c1o
    csn
    #
    cxp
    #
    cun
    #
    @6
    cres
    #
    @13
    cZ
    @18
    @6
    noetalem.2
    reseq1i
    @19
    @13
    @17
    @6
    cres
    #
    cun
    @13
    c0
    cun
    @13
    cS
    @17
    @6
    resundir
    @20
    c0
    @13
    @20
    @17
    @6
    cvv
    cxp
    cin
    #
    c0
    @17
    @6
    df-res
    @15
    @6
    cin
    #
    c0
    wceq
    @21
    c0
    wceq
    @22
    @6
    @15
    cin
    c0
    @15
    @6
    incom
    @6
    @14
    disjdif
    eqtri
    @15
    @6
    @16
    cvv
    xpdisj1
    ax-mp
    eqtri
    uneq2i
    @13
    un0
    3eqtri
    eqtri
    @5
    cS
    wfun
    #
    cS
    wrel
    @13
    cS
    wceq
    @5
    cS
    csur
    wcel
    #
    @23
    @5
    @0
    @1
    @24
    @11
    @12
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
    syl2anc
    #
    cS
    nofun
    syl
    cS
    funrel
    cS
    resdm
    3syl
    syl5eq
    breqtrrd
    @5
    cX
    csur
    wcel
    cZ
    csur
    wcel
    #
    @6
    con0
    wcel
    #
    @9
    @10
    wi
    @3
    cA
    csur
    cX
    @0
    @1
    @2
    simp1
    sselda
    @3
    @26
    @4
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
    adantr
    @5
    @24
    @27
    @25
    cS
    nodmon
    syl
    cX
    cZ
    @6
    sltres
    syl3anc
    mpd
end
