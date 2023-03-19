include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cin.mm"
include "wa.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "2pos.mm"
include "wcel.mm"
include "wne.mm"
include "simprl.mm"
include "wi.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "wn.mm"
include "2re.mm"
include "0re.mm"
include "lenlti.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "adantld.mm"
include "com23.mm"
include "impd.mm"
include "ax-1.mm"
include "pm2.61ine.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "jca.mm"
include "ex.mm"
include "eldifi.mm"
include "anim1i.mm"
include "impbid1.mm"
include "rabbidva2.mm"
include "ax-mp.mm"
include "ineq2i.mm"
include "inrab.mm"
include "cxr.mm"
include "wb.mm"
include "cxnn0.mm"
include "cvv.mm"
include "vex.mm"
include "hashxnn0.mm"
include "xnn0xr.mm"
include "rexri.mm"
include "xrletri3.mm"
include "mp2an.mm"
include "bicomi.mm"
include "rabbii.mm"
include "3eqtri.mm"

theorem umgrislfupgrlem
  let vx: setvar x
  let cV: class V


  assert |- ( { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 } i^i { x e. ~P V | 2 <_ ( # ` x ) } ) = { x e. ( ~P V \ { (/) } ) | ( # ` x ) = 2 }

  proof
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    c2
    @1
    cle
    wbr
    #
    vx
    @3
    crab
    #
    cin
    @6
    @7
    vx
    @5
    crab
    #
    cin
    @2
    @7
    wa
    #
    vx
    @5
    crab
    @1
    c2
    wceq
    #
    vx
    @5
    crab
    @8
    @9
    @6
    cc0
    c2
    clt
    wbr
    #
    @8
    @9
    wceq
    2pos
    @12
    @7
    @7
    vx
    @3
    @5
    @12
    @0
    @3
    wcel
    #
    @7
    wa
    #
    @0
    @5
    wcel
    #
    @7
    wa
    #
    @12
    @14
    @16
    @12
    @14
    wa
    #
    @15
    @7
    @17
    @13
    @0
    c0
    wne
    #
    @15
    @12
    @13
    @7
    simprl
    @17
    @18
    wi
    @0
    c0
    @0
    c0
    wceq
    #
    @12
    @14
    @18
    @19
    @14
    @12
    @18
    @19
    @7
    @12
    @18
    wi
    #
    @13
    @19
    @7
    c2
    cc0
    cle
    wbr
    #
    @20
    @19
    @1
    cc0
    c2
    cle
    @19
    @1
    c0
    chash
    cfv
    cc0
    @0
    c0
    chash
    fveq2
    hash0
    syl6eq
    breq2d
    @21
    @12
    wn
    @20
    c2
    cc0
    2re
    0re
    lenlti
    @12
    @18
    pm2.21
    sylbi
    syl6bi
    adantld
    com23
    impd
    @18
    @17
    ax-1
    pm2.61ine
    @0
    @3
    c0
    eldifsn
    sylanbrc
    @12
    @13
    @7
    simprr
    jca
    ex
    @15
    @13
    @7
    @0
    @3
    @4
    eldifi
    anim1i
    impbid1
    rabbidva2
    ax-mp
    ineq2i
    @2
    @7
    vx
    @5
    inrab
    @10
    @11
    vx
    @5
    @11
    @10
    @1
    cxr
    wcel
    #
    c2
    cxr
    wcel
    @11
    @10
    wb
    @1
    cxnn0
    wcel
    #
    @22
    @0
    cvv
    wcel
    @23
    vx
    vex
    @0
    cvv
    hashxnn0
    ax-mp
    @1
    xnn0xr
    ax-mp
    c2
    2re
    rexri
    @1
    c2
    xrletri3
    mp2an
    bicomi
    rabbii
    3eqtri
end
