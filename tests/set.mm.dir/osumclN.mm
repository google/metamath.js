include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "catm.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "psubclssatN.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "c0.mm"
include "simpll1.mm"
include "oveq1.mm"
include "padd02.mm"
include "sylan9eqr.mm"
include "simpll3.mm"
include "eqeltrd.mm"
include "psubcli2N.mm"
include "wne.mm"
include "osumcllem11N.mm"
include "anassrs.mm"
include "eqcomd.mm"
include "pm2.61dane.mm"
include "wb.mm"
include "ispsubclN.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem osumclN
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


  assert |- ( ( ( K e. HL /\ X e. C /\ Y e. C ) /\ X C_ ( ._|_ ` Y ) ) -> ( X .+ Y ) e. C )

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
    wa
    #
    cX
    cY
    c.pl
    co
    #
    cC
    wcel
    #
    @6
    cK
    catm
    cfv
    #
    wss
    #
    @6
    c.pe
    cfv
    c.pe
    cfv
    #
    @6
    wceq
    #
    @5
    @0
    cX
    @8
    wss
    #
    cY
    @8
    wss
    #
    @9
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    @0
    @1
    @12
    @14
    @0
    @1
    @2
    @4
    simpl2
    @8
    cC
    chlt
    cK
    cX
    @8
    eqid
    #
    osumcl.c
    psubclssatN
    syl2anc
    @5
    @0
    @2
    @13
    @14
    @0
    @1
    @2
    @4
    simpl3
    @8
    cC
    chlt
    cK
    cY
    @15
    osumcl.c
    psubclssatN
    syl2anc
    #
    @8
    chlt
    c.pl
    cK
    cX
    cY
    @15
    osumcl.p
    paddssat
    syl3anc
    @5
    @11
    cX
    c0
    @5
    cX
    c0
    wceq
    #
    wa
    #
    @0
    @7
    @11
    @0
    @1
    @2
    @4
    @17
    simpll1
    @18
    @6
    cY
    cC
    @17
    @5
    @6
    c0
    cY
    c.pl
    co
    #
    cY
    cX
    c0
    cY
    c.pl
    oveq1
    @5
    @0
    @13
    @19
    cY
    wceq
    @14
    @16
    @8
    chlt
    c.pl
    cK
    cY
    @15
    osumcl.p
    padd02
    syl2anc
    sylan9eqr
    @0
    @1
    @2
    @4
    @17
    simpll3
    eqeltrd
    cC
    chlt
    cK
    c.pe
    @6
    osumcl.o
    osumcl.c
    psubcli2N
    syl2anc
    @5
    cX
    c0
    wne
    #
    wa
    @6
    @10
    @3
    @4
    @20
    @6
    @10
    wceq
    cC
    c.pl
    cK
    c.pe
    cX
    cY
    osumcl.p
    osumcl.o
    osumcl.c
    osumcllem11N
    anassrs
    eqcomd
    pm2.61dane
    @5
    @0
    @7
    @9
    @11
    wa
    wb
    @14
    @8
    cC
    chlt
    cK
    c.pe
    @6
    @15
    osumcl.o
    osumcl.c
    ispsubclN
    syl
    mpbir2and
end
