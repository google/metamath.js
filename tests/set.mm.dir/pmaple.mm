include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "catm.mm"
include "cfv.mm"
include "crab.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "cpo.mm"
include "hlpos.mm"
include "eqid.mm"
include "atbase.mm"
include "postr.mm"
include "exp4b.mm"
include "3expd.mm"
include "com23.mm"
include "com34.mm"
include "3imp.mm"
include "syl5.mm"
include "ralrimdv.mm"
include "syl3an1.mm"
include "ss2rab.mm"
include "syl6ibr.mm"
include "club.mm"
include "ccla.mm"
include "hlclat.mm"
include "ssrab2.mm"
include "atssbase.mm"
include "sstri.mm"
include "lubss.mm"
include "mp3an2.mm"
include "ex.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "coml.mm"
include "cal.mm"
include "wceq.mm"
include "hlomcmat.mm"
include "simp2.mm"
include "atlatmstc.mm"
include "syl2anc.mm"
include "simp3.mm"
include "breq12d.mm"
include "sylibd.mm"
include "impbid.mm"
include "pmapval.mm"
include "3adant3.mm"
include "3adant2.mm"
include "sseq12d.mm"
include "bitr4d.mm"

theorem pmaple
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume pmaple.b: |- B = ( Base ` K )
  assume pmaple.l: |- .<_ = ( le ` K )
  assume pmaple.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( M ` X ) C_ ( M ` Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    vp
    cK
    catm
    cfv
    #
    crab
    #
    @5
    cY
    c.le
    wbr
    #
    vp
    @7
    crab
    #
    wss
    #
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    wss
    @3
    @4
    @11
    @3
    @4
    @6
    @9
    wi
    #
    vp
    @7
    wral
    #
    @11
    @0
    cK
    cpo
    wcel
    #
    @1
    @2
    @4
    @15
    wi
    cK
    hlpos
    @16
    @1
    @2
    w3a
    #
    @4
    @14
    vp
    @7
    @17
    @5
    @7
    wcel
    #
    @4
    @14
    @17
    @18
    @6
    @4
    @9
    @18
    @5
    cB
    wcel
    #
    @17
    @6
    @4
    @9
    wi
    wi
    #
    @7
    cB
    @5
    cK
    pmaple.b
    @7
    eqid
    #
    atbase
    @16
    @1
    @2
    @19
    @20
    wi
    @16
    @1
    @19
    @2
    @20
    @16
    @19
    @1
    @2
    @20
    wi
    @16
    @19
    @1
    @2
    @20
    @16
    @19
    @1
    @2
    w3a
    @6
    @4
    @9
    cB
    cK
    c.le
    @5
    cX
    cY
    pmaple.b
    pmaple.l
    postr
    exp4b
    3expd
    com23
    com34
    3imp
    syl5
    com34
    com23
    ralrimdv
    syl3an1
    @6
    @9
    vp
    @7
    ss2rab
    syl6ibr
    @3
    @11
    @8
    cK
    club
    cfv
    #
    cfv
    #
    @10
    @22
    cfv
    #
    c.le
    wbr
    #
    @4
    @0
    @1
    @11
    @25
    wi
    #
    @2
    @0
    cK
    ccla
    wcel
    #
    @26
    cK
    hlclat
    @27
    @11
    @25
    @27
    @10
    cB
    wss
    @11
    @25
    @10
    @7
    cB
    @9
    vp
    @7
    ssrab2
    @7
    cB
    cK
    pmaple.b
    @21
    atssbase
    sstri
    cB
    @8
    @10
    @22
    cK
    c.le
    pmaple.b
    pmaple.l
    @22
    eqid
    #
    lubss
    mp3an2
    ex
    syl
    3ad2ant1
    @3
    @23
    cX
    @24
    cY
    c.le
    @3
    cK
    coml
    wcel
    @27
    cK
    cal
    wcel
    w3a
    #
    @1
    @23
    cX
    wceq
    @0
    @1
    @29
    @2
    cK
    hlomcmat
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    vp
    @7
    cB
    @22
    cK
    c.le
    cX
    pmaple.b
    pmaple.l
    @28
    @21
    atlatmstc
    syl2anc
    @3
    @29
    @2
    @24
    cY
    wceq
    @30
    @0
    @1
    @2
    simp3
    vp
    @7
    cB
    @22
    cK
    c.le
    cY
    pmaple.b
    pmaple.l
    @28
    @21
    atlatmstc
    syl2anc
    breq12d
    sylibd
    impbid
    @3
    @12
    @8
    @13
    @10
    @0
    @1
    @12
    @8
    wceq
    @2
    @7
    cB
    chlt
    cK
    c.le
    cM
    cX
    vp
    pmaple.b
    pmaple.l
    @21
    pmaple.m
    pmapval
    3adant3
    @0
    @2
    @13
    @10
    wceq
    @1
    @7
    cB
    chlt
    cK
    c.le
    cM
    cY
    vp
    pmaple.b
    pmaple.l
    @21
    pmaple.m
    pmapval
    3adant2
    sseq12d
    bitr4d
end
