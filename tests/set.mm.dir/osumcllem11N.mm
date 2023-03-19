include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "co.mm"
include "nonconne.mm"
include "catm.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "psubclssatN.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "2polssN.mm"
include "cv.mm"
include "wrex.mm"
include "wex.mm"
include "wpss.mm"
include "df-pss.mm"
include "pssnel.mm"
include "sylbir.mm"
include "df-rex.mm"
include "sylibr.mm"
include "wi.mm"
include "csn.mm"
include "cjn.mm"
include "cple.mm"
include "osumcllem9N.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "3adantr3.mm"
include "3adant3.mm"
include "polssatN.mm"
include "simp23.mm"
include "sseldd.mm"
include "simp3.mm"
include "osumcllem10N.mm"
include "syl311anc.mm"
include "pm2.21ddne.mm"
include "3exp.mm"
include "3expd.mm"
include "imp32.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "mpand.mm"
include "necon1bd.mm"
include "mpi.mm"

theorem osumcllem11N
  let cC: class C
  let c.pl: class .+
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume osumcl.p: |- .+ = ( +P ` K )
  assume osumcl.o: |- ._|_ = ( _|_P ` K )
  assume osumcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( ( K e. HL /\ X e. C /\ Y e. C ) /\ ( X C_ ( ._|_ ` Y ) /\ X =/= (/) ) ) -> ( X .+ Y ) = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    w3a
    #
    cX
    cY
    c.pe
    cfv
    wss
    #
    cX
    c0
    wne
    #
    wa
    #
    wa
    #
    cX
    cX
    wceq
    cX
    cX
    wne
    wa
    #
    wn
    cX
    cY
    c.pl
    co
    #
    @9
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    wceq
    cX
    cX
    nonconne
    @7
    @8
    @9
    @11
    @7
    @9
    @11
    wss
    #
    @9
    @11
    wne
    #
    @8
    @7
    @0
    @9
    cK
    catm
    cfv
    #
    wss
    #
    @12
    @0
    @1
    @2
    @6
    simpl1
    #
    @7
    @0
    cX
    @14
    wss
    #
    cY
    @14
    wss
    #
    @15
    @16
    @7
    @0
    @1
    @17
    @16
    @0
    @1
    @2
    @6
    simpl2
    @14
    cC
    chlt
    cK
    cX
    @14
    eqid
    #
    osumcl.c
    psubclssatN
    #
    syl2anc
    @7
    @0
    @2
    @18
    @16
    @0
    @1
    @2
    @6
    simpl3
    @14
    cC
    chlt
    cK
    cY
    @19
    osumcl.c
    psubclssatN
    #
    syl2anc
    @14
    chlt
    c.pl
    cK
    cX
    cY
    @19
    osumcl.p
    paddssat
    syl3anc
    #
    @14
    cK
    c.pe
    @9
    @19
    osumcl.o
    2polssN
    syl2anc
    @12
    @13
    wa
    #
    vp
    cv
    #
    @9
    wcel
    wn
    #
    vp
    @11
    wrex
    #
    @7
    @8
    @23
    @24
    @11
    wcel
    #
    @25
    wa
    vp
    wex
    #
    @26
    @23
    @9
    @11
    wpss
    @28
    @9
    @11
    df-pss
    vp
    @9
    @11
    pssnel
    sylbir
    @25
    vp
    @11
    df-rex
    sylibr
    @7
    @25
    @8
    vp
    @11
    @3
    @4
    @5
    @27
    @25
    @8
    wi
    #
    wi
    @3
    @4
    @5
    @27
    @29
    @3
    @4
    @5
    @27
    w3a
    #
    @25
    @8
    @3
    @30
    @25
    w3a
    #
    @8
    cX
    @24
    csn
    c.pl
    co
    #
    cX
    @14
    cC
    c.pl
    @11
    cK
    cjn
    cfv
    #
    cK
    cK
    cple
    cfv
    #
    @32
    c.pe
    cX
    cY
    vp
    @34
    eqid
    #
    @33
    eqid
    #
    @19
    osumcl.p
    osumcl.o
    osumcl.c
    @32
    eqid
    #
    @11
    eqid
    #
    osumcllem9N
    @31
    @0
    @17
    @18
    @24
    @14
    wcel
    @25
    @32
    cX
    wne
    @0
    @1
    @2
    @30
    @25
    simp11
    #
    @31
    @0
    @1
    @17
    @39
    @0
    @1
    @2
    @30
    @25
    simp12
    @20
    syl2anc
    @31
    @0
    @2
    @18
    @39
    @0
    @1
    @2
    @30
    @25
    simp13
    @21
    syl2anc
    @31
    @11
    @14
    @24
    @31
    @0
    @10
    @14
    wss
    #
    @11
    @14
    wss
    @39
    @31
    @0
    @15
    @40
    @39
    @3
    @30
    @15
    @25
    @3
    @4
    @5
    @15
    @27
    @22
    3adantr3
    3adant3
    @14
    cK
    c.pe
    @9
    @19
    osumcl.o
    polssatN
    syl2anc
    @14
    cK
    c.pe
    @10
    @19
    osumcl.o
    polssatN
    syl2anc
    @3
    @4
    @5
    @27
    @25
    simp23
    sseldd
    @3
    @30
    @25
    simp3
    @14
    cC
    c.pl
    @11
    @33
    cK
    @34
    @32
    c.pe
    cX
    cY
    vp
    @35
    @36
    @19
    osumcl.p
    osumcl.o
    osumcl.c
    @37
    @38
    osumcllem10N
    syl311anc
    pm2.21ddne
    3exp
    3expd
    imp32
    rexlimdv
    syl5
    mpand
    necon1bd
    mpi
end
