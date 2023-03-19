include "wac.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "cgrp.mm"
include "cima.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "dfac10.mm"
include "cv.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "wrex.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "basfn.mm"
include "ssv.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "eqid.mm"
include "grpbn0.mm"
include "neeq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "adantl.mm"
include "vex.mm"
include "jctil.mm"
include "cabl.mm"
include "ablgrp.mm"
include "ssriv.mm"
include "imass2.mm"
include "ax-mp.mm"
include "simprl.mm"
include "simpl.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "isnumbasgrplem3.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "impbida.mm"
include "eldifsn.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "char.mm"
include "cun.mm"
include "fvex.mm"
include "unex.mm"
include "ssun2.mm"
include "harn0.mm"
include "ssn0.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "id.mm"
include "isnumbasgrp.mm"
include "sylibr.mm"
include "2thd.mm"
include "impbii.mm"
include "bitri.mm"

theorem dfacbasgrp
  let vx: setvar x
  let vy: setvar y


  assert |- ( CHOICE <-> ( Base " Grp ) = ( _V \ { (/) } ) )

  proof
    wac
    ccrd
    cdm
    #
    cvv
    wceq
    #
    cbs
    cgrp
    cima
    #
    cvv
    c0
    csn
    cdif
    #
    wceq
    #
    dfac10
    @1
    @4
    @1
    vx
    @2
    @3
    @1
    vx
    cv
    #
    @2
    wcel
    #
    @5
    cvv
    wcel
    #
    @5
    c0
    wne
    #
    wa
    #
    @5
    @3
    wcel
    @1
    @6
    @9
    @1
    @6
    wa
    @8
    @7
    @6
    @8
    @1
    @6
    vy
    cv
    #
    cbs
    cfv
    #
    @5
    wceq
    #
    vy
    cgrp
    wrex
    #
    @8
    cbs
    cvv
    wfn
    cgrp
    cvv
    wss
    @6
    @13
    wb
    basfn
    cgrp
    ssv
    vy
    cvv
    cgrp
    @5
    cbs
    fvelimab
    mp2an
    @12
    @8
    vy
    cgrp
    @10
    cgrp
    wcel
    @11
    c0
    wne
    @12
    @8
    @11
    @10
    @11
    eqid
    grpbn0
    @11
    @5
    c0
    neeq1
    syl5ibcom
    rexlimiv
    sylbi
    adantl
    vx
    vex
    #
    jctil
    @1
    @9
    wa
    #
    cbs
    cabl
    cima
    #
    @2
    @5
    cabl
    cgrp
    wss
    @16
    @2
    wss
    vx
    cabl
    cgrp
    @5
    ablgrp
    ssriv
    cabl
    cgrp
    cbs
    imass2
    ax-mp
    @15
    @5
    @0
    wcel
    #
    @8
    @5
    @16
    wcel
    @15
    @5
    cvv
    @0
    @1
    @7
    @8
    simprl
    @1
    @9
    simpl
    eleqtrrd
    @1
    @7
    @8
    simprr
    @5
    isnumbasgrplem3
    syl2anc
    sseldi
    impbida
    @5
    cvv
    c0
    eldifsn
    syl6bbr
    eqrdv
    @4
    vx
    @0
    cvv
    @4
    @17
    @7
    @4
    @5
    @5
    char
    cfv
    #
    cun
    #
    @2
    wcel
    @17
    @4
    @19
    @3
    @2
    @19
    @3
    wcel
    #
    @4
    @20
    @19
    cvv
    wcel
    @19
    c0
    wne
    #
    @5
    @18
    @14
    @5
    char
    fvex
    unex
    @18
    @19
    wss
    @18
    c0
    wne
    #
    @21
    @18
    @5
    ssun2
    @7
    @22
    @14
    @5
    cvv
    harn0
    ax-mp
    @18
    @19
    ssn0
    mp2an
    @19
    cvv
    c0
    eldifsn
    mpbir2an
    a1i
    @4
    id
    eleqtrrd
    @5
    isnumbasgrp
    sylibr
    @7
    @4
    @14
    a1i
    2thd
    eqrdv
    impbii
    bitri
end
