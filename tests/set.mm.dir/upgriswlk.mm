include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "iswlkg.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-ifp.mm"
include "wi.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "a1d.mm"
include "cedg.mm"
include "eqid.mm"
include "upgredginwlk.mm"
include "adantrr.mm"
include "imp.mm"
include "cvv.mm"
include "wne.mm"
include "simp-4l.mm"
include "simpr.mm"
include "adantr.mm"
include "adantl.mm"
include "fvexd.mm"
include "neqne.mm"
include "3jca.mm"
include "upgredgpr.mm"
include "syl31anc.mm"
include "eqcomd.mm"
include "exp31.mm"
include "mpd.mm"
include "com12.mm"
include "jaoi.mm"
include "syl5bi.mm"
include "ifpprsnss.mm"
include "impbid1.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem upgriswlk
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  assume upgriswlk.v: |- V = ( Vtx ` G )
  assume upgriswlk.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint I k
  disjoint P k
  disjoint V k
  assert |- ( G e. UPGraph -> ( F ( Walks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    vk
    cv
    #
    cP
    cfv
    #
    @4
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @4
    cF
    cfv
    cI
    cfv
    #
    @5
    csn
    #
    wceq
    #
    @5
    @7
    cpr
    #
    @9
    wss
    #
    wif
    #
    vk
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @1
    @3
    @9
    @12
    wceq
    #
    vk
    @15
    wral
    #
    w3a
    #
    cP
    vk
    cF
    cG
    cI
    cV
    cupgr
    upgriswlk.v
    upgriswlk.i
    iswlkg
    @0
    @1
    @3
    wa
    #
    @16
    wa
    @21
    @19
    wa
    @17
    @20
    @0
    @21
    @16
    @19
    @0
    @21
    wa
    #
    @14
    @18
    vk
    @15
    @22
    @4
    @15
    wcel
    #
    wa
    #
    @14
    @18
    @14
    @8
    @11
    wa
    #
    @8
    wn
    #
    @13
    wa
    #
    wo
    #
    @24
    @18
    @8
    @11
    @13
    df-ifp
    @28
    @24
    @18
    @25
    @24
    @18
    wi
    @27
    @25
    @18
    @24
    @8
    @11
    @18
    @8
    @10
    @12
    @9
    @8
    @10
    @5
    @5
    cpr
    @12
    @5
    dfsn2
    @5
    @7
    @5
    preq2
    syl5eq
    eqeq2d
    biimpa
    a1d
    @24
    @27
    @18
    @24
    @9
    cG
    cedg
    cfv
    #
    wcel
    #
    @27
    @18
    wi
    @22
    @23
    @30
    @0
    @1
    @23
    @30
    wi
    @3
    @29
    cF
    cG
    cI
    @4
    upgriswlk.i
    @29
    eqid
    #
    upgredginwlk
    adantrr
    imp
    @24
    @30
    @27
    @18
    @24
    @30
    wa
    #
    @27
    wa
    #
    @12
    @9
    @33
    @0
    @30
    @13
    @5
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    @5
    @7
    wne
    #
    w3a
    #
    @12
    @9
    wceq
    @0
    @21
    @23
    @30
    @27
    simp-4l
    @32
    @30
    @27
    @24
    @30
    simpr
    adantr
    @27
    @13
    @32
    @26
    @13
    simpr
    adantl
    @27
    @37
    @32
    @26
    @37
    @13
    @26
    @34
    @35
    @36
    @26
    @4
    cP
    fvexd
    @26
    @6
    cP
    fvexd
    @5
    @7
    neqne
    3jca
    adantr
    adantl
    @5
    @7
    @9
    cvv
    @29
    cG
    cV
    cvv
    upgriswlk.v
    @31
    upgredgpr
    syl31anc
    eqcomd
    exp31
    mpd
    com12
    jaoi
    com12
    syl5bi
    @5
    @7
    @9
    ifpprsnss
    impbid1
    ralbidva
    pm5.32da
    @1
    @3
    @16
    df-3an
    @1
    @3
    @19
    df-3an
    3bitr4g
    bitrd
end
