include "chlt.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cfv.mm"
include "ciin.mm"
include "cin.mm"
include "c0.mm"
include "wi.mm"
include "cops.mm"
include "hlop.mm"
include "cp1.mm"
include "eqid.mm"
include "glb0N.mm"
include "fveq2d.mm"
include "pmap1N.mm"
include "eqtrd.mm"
include "syl.mm"
include "rexeq.mm"
include "abbidv.mm"
include "rex0.mm"
include "abf.mm"
include "syl6eq.mm"
include "riin0.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "wne.mm"
include "w3a.mm"
include "pmapglbx.mm"
include "wss.mm"
include "wex.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpr.mm"
include "simpll.mm"
include "rspa.mm"
include "adantll.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "jca.mm"
include "ex.mm"
include "eximd.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "3impia.mm"
include "iinss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "pm2.61dne.mm"

theorem pmapglb2xN
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cK: class K
  let cM: class M
  let vx: setvar x
  assume pmapglb2.b: |- B = ( Base ` K )
  assume pmapglb2.g: |- G = ( glb ` K )
  assume pmapglb2.a: |- A = ( Atoms ` K )
  assume pmapglb2.m: |- M = ( pmap ` K )

  disjoint A i
  disjoint i y
  disjoint B i
  disjoint B y
  disjoint I i
  disjoint I y
  disjoint K i
  disjoint K y
  disjoint S y
  disjoint i x
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint K x
  disjoint S x
  assert |- ( ( K e. HL /\ A. i e. I S e. B ) -> ( M ` ( G ` { y | E. i e. I y = S } ) ) = ( A i^i |^|_ i e. I ( M ` S ) ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cB
    wcel
    #
    vi
    cI
    wral
    #
    wa
    #
    vy
    cv
    cS
    wceq
    #
    vi
    cI
    wrex
    #
    vy
    cab
    #
    cG
    cfv
    #
    cM
    cfv
    #
    cA
    vi
    cI
    cS
    cM
    cfv
    #
    ciin
    #
    cin
    #
    wceq
    #
    cI
    c0
    @0
    cI
    c0
    wceq
    #
    @12
    wi
    @2
    @0
    @12
    @13
    c0
    cG
    cfv
    #
    cM
    cfv
    #
    cA
    wceq
    #
    @0
    cK
    cops
    wcel
    #
    @16
    cK
    hlop
    @17
    @15
    cK
    cp1
    cfv
    #
    cM
    cfv
    cA
    @17
    @14
    @18
    cM
    @18
    cG
    cK
    pmapglb2.g
    @18
    eqid
    #
    glb0N
    fveq2d
    cA
    @18
    cK
    cM
    @19
    pmapglb2.a
    pmapglb2.m
    pmap1N
    eqtrd
    syl
    @13
    @8
    @15
    @11
    cA
    @13
    @7
    @14
    cM
    @13
    @6
    c0
    cG
    @13
    @6
    @4
    vi
    c0
    wrex
    #
    vy
    cab
    c0
    @13
    @5
    @20
    vy
    @4
    vi
    cI
    c0
    rexeq
    abbidv
    @20
    vy
    @4
    vi
    rex0
    abf
    syl6eq
    fveq2d
    fveq2d
    vi
    cA
    @9
    cI
    riin0
    eqeq12d
    syl5ibrcom
    adantr
    @0
    @2
    cI
    c0
    wne
    #
    @12
    @0
    @2
    @21
    w3a
    #
    @8
    @10
    @11
    vy
    cB
    cS
    vi
    cG
    cI
    cK
    cM
    pmapglb2.b
    pmapglb2.g
    pmapglb2.m
    pmapglbx
    @22
    @10
    cA
    wss
    #
    @11
    @10
    wceq
    @22
    @9
    cA
    wss
    #
    vi
    cI
    wrex
    #
    @23
    @0
    @2
    @21
    @25
    @3
    vi
    cv
    cI
    wcel
    #
    vi
    wex
    @26
    @24
    wa
    #
    vi
    wex
    @21
    @25
    @3
    @26
    @27
    vi
    @0
    @2
    vi
    @0
    vi
    nfv
    @1
    vi
    cI
    nfra1
    nfan
    @3
    @26
    @27
    @3
    @26
    wa
    #
    @26
    @24
    @3
    @26
    simpr
    @28
    @0
    @1
    @24
    @0
    @2
    @26
    simpll
    @2
    @26
    @1
    @0
    @1
    vi
    cI
    rspa
    adantll
    cA
    cB
    chlt
    cK
    cM
    cS
    pmapglb2.b
    pmapglb2.a
    pmapglb2.m
    pmapssat
    syl2anc
    jca
    ex
    eximd
    vi
    cI
    n0
    @24
    vi
    cI
    df-rex
    3imtr4g
    3impia
    vi
    cI
    @9
    cA
    iinss
    syl
    @10
    cA
    sseqin2
    sylib
    eqtr4d
    3expia
    pm2.61dne
end
