include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "clsm.mm"
include "co.mm"
include "wrex.mm"
include "clss.mm"
include "wcel.mm"
include "w3a.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "islshpsm.mm"
include "mpbid.mm"
include "simp3d.mm"
include "adantr.mm"
include "wpss.mm"
include "wss.mm"
include "id.mm"
include "adantlr.mm"
include "3adant3.mm"
include "chlt.mm"
include "lshplss.mm"
include "lssss.mm"
include "syl.mm"
include "dochocss.mm"
include "syl2anc.mm"
include "3ad2ant1.mm"
include "simp1r.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "dochssv.mm"
include "simp3.mm"
include "sseqtr4d.mm"
include "dvhlvec.mm"
include "dochlss.mm"
include "simpr.mm"
include "lsmcv.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "lshpne.mm"
include "eqnetrd.mm"
include "impbida.mm"

theorem dochshpncl
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vv: setvar v
  assume dochshpncl.h: |- H = ( LHyp ` K )
  assume dochshpncl.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochshpncl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochshpncl.v: |- V = ( Base ` U )
  assume dochshpncl.y: |- Y = ( LSHyp ` U )
  assume dochshpncl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochshpncl.x: |- ( ph -> X e. Y )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` X ) ) =/= X <-> ( ._|_ ` ( ._|_ ` X ) ) = V ) )

  proof
    wph
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wne
    #
    @1
    cV
    wceq
    #
    wph
    @2
    wa
    #
    cX
    vv
    cv
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    cU
    clsm
    cfv
    #
    co
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    @3
    wph
    @10
    @2
    wph
    cX
    cU
    clss
    cfv
    #
    wcel
    #
    cX
    cV
    wne
    #
    @10
    wph
    cX
    cY
    wcel
    @12
    @13
    @10
    w3a
    dochshpncl.x
    wph
    vv
    @7
    @11
    cX
    cY
    @6
    cV
    cU
    dochshpncl.v
    @6
    eqid
    #
    @11
    eqid
    #
    @7
    eqid
    #
    dochshpncl.y
    wph
    cU
    cH
    cK
    cW
    dochshpncl.h
    dochshpncl.u
    dochshpncl.k
    dvhlmod
    #
    islshpsm
    mpbid
    simp3d
    adantr
    @4
    @9
    @3
    vv
    cV
    @4
    @5
    cV
    wcel
    #
    @9
    w3a
    #
    @1
    @8
    cV
    @19
    wph
    @18
    wa
    #
    cX
    @1
    wpss
    #
    @1
    @8
    wss
    @1
    @8
    wceq
    @4
    @18
    @20
    @9
    wph
    @18
    @20
    @2
    @20
    id
    adantlr
    3adant3
    @19
    cX
    @1
    wss
    #
    cX
    @1
    wne
    @21
    @4
    @18
    @22
    @9
    wph
    @22
    @2
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    @22
    dochshpncl.k
    wph
    @12
    @24
    wph
    @11
    cX
    cY
    cU
    @15
    dochshpncl.y
    @17
    dochshpncl.x
    lshplss
    #
    @11
    cX
    cV
    cU
    dochshpncl.v
    @15
    lssss
    syl
    #
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochshpncl.h
    dochshpncl.u
    dochshpncl.v
    dochshpncl.o
    dochocss
    syl2anc
    adantr
    3ad2ant1
    @19
    @1
    cX
    wph
    @2
    @18
    @9
    simp1r
    necomd
    cX
    @1
    df-pss
    sylanbrc
    @19
    @1
    cV
    @8
    @4
    @18
    @1
    cV
    wss
    #
    @9
    wph
    @27
    @2
    wph
    @23
    @0
    cV
    wss
    #
    @27
    dochshpncl.k
    wph
    @23
    @24
    @28
    dochshpncl.k
    @26
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochshpncl.h
    dochshpncl.u
    dochshpncl.v
    dochshpncl.o
    dochssv
    syl2anc
    #
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    dochshpncl.h
    dochshpncl.u
    dochshpncl.v
    dochshpncl.o
    dochssv
    syl2anc
    adantr
    3ad2ant1
    @4
    @18
    @9
    simp3
    #
    sseqtr4d
    @20
    @7
    @11
    cX
    @1
    @6
    cV
    cU
    @5
    dochshpncl.v
    @15
    @14
    @16
    @20
    cU
    cH
    cK
    cW
    dochshpncl.h
    dochshpncl.u
    wph
    @23
    @18
    dochshpncl.k
    adantr
    dvhlvec
    wph
    @12
    @18
    @25
    adantr
    wph
    @1
    @11
    wcel
    #
    @18
    wph
    @23
    @28
    @31
    dochshpncl.k
    @29
    @11
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    dochshpncl.h
    dochshpncl.u
    dochshpncl.v
    @15
    dochshpncl.o
    dochlss
    syl2anc
    adantr
    wph
    @18
    simpr
    lsmcv
    syl3anc
    @30
    eqtrd
    rexlimdv3a
    mpd
    wph
    @3
    wa
    #
    @1
    cV
    cX
    wph
    @3
    simpr
    @32
    cX
    cV
    wph
    @13
    @3
    wph
    cX
    cY
    cV
    cU
    dochshpncl.v
    dochshpncl.y
    @17
    dochshpncl.x
    lshpne
    adantr
    necomd
    eqnetrd
    impbida
end
