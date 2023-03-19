include "c1.mm"
include "wcel.mm"
include "chash.mm"
include "cpw.mm"
include "cres.mm"
include "cvol.mm"
include "wne.mm"
include "csn.mm"
include "cfv.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "wceq.mm"
include "snelpwi.mm"
include "fvres.mm"
include "syl.mm"
include "cr.mm"
include "1re.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "cdm.mm"
include "wss.mm"
include "covol.mm"
include "snssi.mm"
include "ovolsn.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "mblvol.mm"
include "mp2b.mm"
include "3netr4d.mm"
include "fveq1.mm"
include "necon3i.mm"
include "wn.mm"
include "wa.mm"
include "biantrur.mm"
include "snex.mm"
include "elpw.mm"
include "dmhashres.mm"
include "eleq2i.mm"
include "1ex.mm"
include "snss.mm"
include "3bitr4i.mm"
include "notbii.mm"
include "bitr3i.mm"
include "nelne1.mm"
include "sylbir.mm"
include "necomd.mm"
include "dmeq.mm"
include "pm2.61i.mm"

theorem cntnevol
  let cO: class O


  assert |- ( # |` ~P O ) =/= vol

  proof
    c1
    cO
    wcel
    #
    chash
    cO
    cpw
    #
    cres
    #
    cvol
    wne
    #
    @0
    c1
    csn
    #
    @2
    cfv
    #
    @4
    cvol
    cfv
    #
    wne
    @3
    @0
    c1
    cc0
    @5
    @6
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    @0
    @5
    @4
    chash
    cfv
    #
    c1
    @0
    @4
    @1
    wcel
    #
    @5
    @7
    wceq
    c1
    cO
    snelpwi
    @4
    @1
    chash
    fvres
    syl
    c1
    cr
    wcel
    #
    @7
    c1
    wceq
    1re
    c1
    cr
    hashsng
    ax-mp
    syl6eq
    @6
    cc0
    wceq
    #
    @0
    @9
    @4
    cvol
    cdm
    #
    wcel
    #
    @10
    1re
    @9
    @4
    cr
    wss
    @4
    covol
    cfv
    #
    cc0
    wceq
    #
    @12
    c1
    cr
    snssi
    c1
    ovolsn
    #
    @4
    nulmbl
    syl2anc
    #
    @12
    @6
    @13
    cc0
    @4
    mblvol
    @9
    @14
    1re
    @15
    ax-mp
    syl6eq
    mp2b
    a1i
    3netr4d
    @2
    cvol
    @5
    @6
    @4
    @2
    cvol
    fveq1
    necon3i
    syl
    @0
    wn
    #
    @2
    cdm
    #
    @11
    wne
    @3
    @17
    @11
    @18
    @17
    @12
    @4
    @18
    wcel
    #
    wn
    #
    wa
    #
    @11
    @18
    wne
    @21
    @20
    @17
    @12
    @20
    @9
    @12
    1re
    @16
    ax-mp
    biantrur
    @19
    @0
    @8
    @4
    cO
    wss
    @19
    @0
    @4
    cO
    c1
    snex
    elpw
    @18
    @1
    @4
    @1
    dmhashres
    eleq2i
    c1
    cO
    1ex
    snss
    3bitr4i
    notbii
    bitr3i
    @4
    @11
    @18
    nelne1
    sylbir
    necomd
    @2
    cvol
    @18
    @11
    @2
    cvol
    dmeq
    necon3i
    syl
    pm2.61i
end
