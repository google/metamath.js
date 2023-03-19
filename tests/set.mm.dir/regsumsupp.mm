include "cr.mm"
include "wf.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wcel.mm"
include "w3a.mm"
include "crefld.mm"
include "cgsu.mm"
include "co.mm"
include "ccnfld.mm"
include "csupp.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csu.mm"
include "cc.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "simp3.mm"
include "wss.mm"
include "simp1.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "ssid.mm"
include "a1i.mm"
include "simp2.mm"
include "gsumres.mm"
include "caddc.mm"
include "cvv.mm"
include "cnfldadd.mm"
include "df-refld.mm"
include "cnfldex.mm"
include "0red.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "addid2d.mm"
include "addid1d.mm"
include "jca.mm"
include "gsumress.mm"
include "eqtr2d.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "cfn.mm"
include "id.mm"
include "fsuppimpd.mm"
include "3ad2ant2.mm"
include "simpl1.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "gsumfsum.mm"
include "3eqtrd.mm"

theorem regsumsupp
  let vx: setvar x
  let cF: class F
  let cI: class I
  let cV: class V

  disjoint F x
  disjoint I x
  disjoint V x
  assert |- ( ( F : I --> RR /\ F finSupp 0 /\ I e. V ) -> ( RRfld gsum F ) = sum_ x e. ( F supp 0 ) ( F ` x ) )

  proof
    cI
    cr
    cF
    wf
    #
    cF
    cc0
    cfsupp
    wbr
    #
    cI
    cV
    wcel
    #
    w3a
    #
    crefld
    cF
    cgsu
    co
    #
    ccnfld
    cF
    cF
    cc0
    csupp
    co
    #
    cres
    #
    cgsu
    co
    #
    ccnfld
    vx
    @5
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cgsu
    co
    @5
    @9
    vx
    csu
    @3
    @7
    ccnfld
    cF
    cgsu
    co
    @4
    @3
    cI
    cc
    cF
    ccnfld
    cV
    @5
    cc0
    cnfldbas
    cnfld0
    ccnfld
    crg
    wcel
    ccnfld
    ccmn
    wcel
    @3
    cnring
    ccnfld
    ringcmn
    mp1i
    @0
    @1
    @2
    simp3
    #
    @3
    @0
    cr
    cc
    wss
    #
    cI
    cc
    cF
    wf
    @0
    @1
    @2
    simp1
    #
    ax-resscn
    cI
    cr
    cc
    cF
    fss
    sylancl
    @5
    @5
    wss
    @3
    @5
    ssid
    a1i
    @0
    @1
    @2
    simp2
    gsumres
    @3
    vx
    cI
    cc
    caddc
    cr
    cF
    ccnfld
    crefld
    cvv
    cV
    cc0
    cnfldbas
    cnfldadd
    df-refld
    ccnfld
    cvv
    wcel
    @3
    cnfldex
    a1i
    @11
    @12
    @3
    ax-resscn
    a1i
    @13
    @3
    0red
    @3
    @8
    cc
    wcel
    #
    wa
    #
    cc0
    @8
    caddc
    co
    @8
    wceq
    @8
    cc0
    caddc
    co
    @8
    wceq
    @15
    @8
    @3
    @14
    simpr
    #
    addid2d
    @15
    @8
    @16
    addid1d
    jca
    gsumress
    eqtr2d
    @3
    @6
    @10
    ccnfld
    cgsu
    @3
    vx
    cI
    cr
    @5
    cF
    @13
    @3
    cF
    cdm
    #
    @5
    cI
    cF
    cc0
    suppssdm
    @3
    @0
    @17
    cI
    wceq
    @13
    cI
    cr
    cF
    fdm
    syl
    syl5sseq
    #
    feqresmpt
    oveq2d
    @3
    @5
    @9
    vx
    @1
    @0
    @5
    cfn
    wcel
    @2
    @1
    cF
    cc0
    @1
    id
    fsuppimpd
    3ad2ant2
    @3
    @8
    @5
    wcel
    #
    wa
    #
    @9
    @20
    cI
    cr
    @8
    cF
    @0
    @1
    @2
    @19
    simpl1
    @3
    @5
    cI
    @8
    @18
    sselda
    ffvelrnd
    recnd
    gsumfsum
    3eqtrd
end
