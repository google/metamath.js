include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "wceq.mm"
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
include "fveq2.mm"
include "riin0.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "wne.mm"
include "w3a.mm"
include "pmapglb.mm"
include "wrex.mm"
include "wex.mm"
include "simpr.mm"
include "simpll.mm"
include "ssel2.mm"
include "adantll.mm"
include "pmapssat.mm"
include "syl2anc.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
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

theorem pmapglb2N
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let cM: class M
  let vi: setvar i
  let vy: setvar y
  let cI: class I
  assume pmapglb2.b: |- B = ( Base ` K )
  assume pmapglb2.g: |- G = ( glb ` K )
  assume pmapglb2.a: |- A = ( Atoms ` K )
  assume pmapglb2.m: |- M = ( pmap ` K )

  disjoint A x
  disjoint B x
  disjoint K x
  disjoint S x
  disjoint i x
  disjoint A i
  disjoint i y
  disjoint B i
  disjoint x y
  disjoint B y
  disjoint I i
  disjoint I y
  disjoint K i
  disjoint K y
  disjoint S y
  assert |- ( ( K e. HL /\ S C_ B ) -> ( M ` ( G ` S ) ) = ( A i^i |^|_ x e. S ( M ` x ) ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cS
    cG
    cfv
    #
    cM
    cfv
    #
    cA
    vx
    cS
    vx
    cv
    #
    cM
    cfv
    #
    ciin
    #
    cin
    #
    wceq
    #
    cS
    c0
    @0
    cS
    c0
    wceq
    #
    @9
    wi
    @1
    @0
    @9
    @10
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
    @13
    cK
    hlop
    @14
    @12
    cK
    cp1
    cfv
    #
    cM
    cfv
    cA
    @14
    @11
    @15
    cM
    @15
    cG
    cK
    pmapglb2.g
    @15
    eqid
    #
    glb0N
    fveq2d
    cA
    @15
    cK
    cM
    @16
    pmapglb2.a
    pmapglb2.m
    pmap1N
    eqtrd
    syl
    @10
    @4
    @12
    @8
    cA
    @10
    @3
    @11
    cM
    cS
    c0
    cG
    fveq2
    fveq2d
    vx
    cA
    @6
    cS
    riin0
    eqeq12d
    syl5ibrcom
    adantr
    @0
    @1
    cS
    c0
    wne
    #
    @9
    @0
    @1
    @17
    w3a
    #
    @4
    @7
    @8
    vx
    cB
    cS
    cG
    cK
    cM
    pmapglb2.b
    pmapglb2.g
    pmapglb2.m
    pmapglb
    @18
    @7
    cA
    wss
    #
    @8
    @7
    wceq
    @18
    @6
    cA
    wss
    #
    vx
    cS
    wrex
    #
    @19
    @0
    @1
    @17
    @21
    @2
    @5
    cS
    wcel
    #
    vx
    wex
    @22
    @20
    wa
    #
    vx
    wex
    @17
    @21
    @2
    @22
    @23
    vx
    @2
    @22
    @23
    @2
    @22
    wa
    #
    @22
    @20
    @2
    @22
    simpr
    @24
    @0
    @5
    cB
    wcel
    #
    @20
    @0
    @1
    @22
    simpll
    @1
    @22
    @25
    @0
    cS
    cB
    @5
    ssel2
    adantll
    cA
    cB
    chlt
    cK
    cM
    @5
    pmapglb2.b
    pmapglb2.a
    pmapglb2.m
    pmapssat
    syl2anc
    jca
    ex
    eximdv
    vx
    cS
    n0
    @20
    vx
    cS
    df-rex
    3imtr4g
    3impia
    vx
    cS
    @6
    cA
    iinss
    syl
    @7
    cA
    sseqin2
    sylib
    eqtr4d
    3expia
    pm2.61dne
end
