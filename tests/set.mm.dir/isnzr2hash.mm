include "cnzr.mm"
include "wcel.mm"
include "crg.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "chash.mm"
include "clt.mm"
include "wbr.mm"
include "eqid.mm"
include "isnzr.mm"
include "wi.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "cpr.mm"
include "cxr.mm"
include "1re.mm"
include "rexri.mm"
include "a1i.mm"
include "cvv.mm"
include "prex.mm"
include "hashxrcl.mm"
include "mp1i.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c2.mm"
include "1lt2.mm"
include "wceq.mm"
include "hashprg.mm"
include "biimpa.mm"
include "syl5breqr.mm"
include "wss.mm"
include "cle.mm"
include "simpl.mm"
include "prss.mm"
include "sylib.mm"
include "hashss.mm"
include "sylancr.mm"
include "xrltletrd.mm"
include "ex.mm"
include "syl2anc.mm"
include "imdistani.mm"
include "ring1ne0.mm"
include "jca.mm"
include "impbii.mm"
include "bitri.mm"

theorem isnzr2hash
  let cB: class B
  let cR: class R
  assume isnzr2hash.b: |- B = ( Base ` R )


  assert |- ( R e. NzRing <-> ( R e. Ring /\ 1 < ( # ` B ) ) )

  proof
    cR
    cnzr
    wcel
    cR
    crg
    wcel
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    wne
    #
    wa
    #
    @0
    c1
    cB
    chash
    cfv
    #
    clt
    wbr
    #
    wa
    #
    cR
    @1
    @2
    @1
    eqid
    #
    @2
    eqid
    #
    isnzr
    @4
    @7
    @0
    @3
    @6
    @0
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @3
    @6
    wi
    cB
    cR
    @1
    isnzr2hash.b
    @8
    ringidcl
    cB
    cR
    @2
    isnzr2hash.b
    @9
    ring0cl
    @10
    @11
    wa
    #
    @3
    @6
    @12
    @3
    wa
    #
    c1
    @1
    @2
    cpr
    #
    chash
    cfv
    #
    @5
    c1
    cxr
    wcel
    @13
    c1
    1re
    rexri
    a1i
    @14
    cvv
    wcel
    @15
    cxr
    wcel
    @13
    @1
    @2
    prex
    @14
    cvv
    hashxrcl
    mp1i
    cB
    cvv
    wcel
    #
    @5
    cxr
    wcel
    @13
    cB
    cR
    cbs
    cfv
    cvv
    isnzr2hash.b
    cR
    cbs
    fvex
    eqeltri
    #
    cB
    cvv
    hashxrcl
    mp1i
    @13
    c1
    c2
    @15
    clt
    1lt2
    @12
    @3
    @15
    c2
    wceq
    @1
    @2
    cB
    cB
    hashprg
    biimpa
    syl5breqr
    @13
    @16
    @14
    cB
    wss
    #
    @15
    @5
    cle
    wbr
    @17
    @13
    @12
    @18
    @12
    @3
    simpl
    @1
    @2
    cB
    cR
    cur
    fvex
    cR
    c0g
    fvex
    prss
    sylib
    cB
    @14
    cvv
    hashss
    sylancr
    xrltletrd
    ex
    syl2anc
    imdistani
    @7
    @0
    @3
    @0
    @6
    simpl
    cB
    cR
    @1
    @2
    isnzr2hash.b
    @8
    @9
    ring1ne0
    jca
    impbii
    bitri
end
