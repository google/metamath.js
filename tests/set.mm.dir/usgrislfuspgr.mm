include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wa.mm"
include "usgruspgr.mm"
include "wceq.mm"
include "wf1.mm"
include "usgrfs.mm"
include "f1f.mm"
include "wss.mm"
include "wi.mm"
include "2re.mm"
include "leidi.mm"
include "a1i.mm"
include "breq2.mm"
include "mpbird.mm"
include "ss2rabi.mm"
include "fssd.mm"
include "syl.mm"
include "jca.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "uspgrf.mm"
include "ccnv.mm"
include "wfun.mm"
include "df-f1.mm"
include "cin.mm"
include "fin.mm"
include "wb.mm"
include "umgrislfupgrlem.mm"
include "feq3.mm"
include "ax-mp.mm"
include "sylbb1.mm"
include "anim1i.mm"
include "sylibr.mm"
include "ex.mm"
include "impancom.mm"
include "sylbi.mm"
include "imp.mm"
include "sylan.mm"
include "isusgr.mm"
include "adantr.mm"
include "impbii.mm"

theorem usgrislfuspgr
  let vx: setvar x
  let cG: class G
  let cI: class I
  let cV: class V
  assume usgrislfuspgr.v: |- V = ( Vtx ` G )
  assume usgrislfuspgr.i: |- I = ( iEdg ` G )

  disjoint G x
  disjoint V x
  assert |- ( G e. USGraph <-> ( G e. USPGraph /\ I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } ) )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cuspgr
    wcel
    #
    cI
    cdm
    #
    c2
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    crab
    #
    cI
    wf
    #
    wa
    #
    @0
    @1
    @8
    cG
    usgruspgr
    @0
    @2
    @4
    c2
    wceq
    #
    vx
    @6
    crab
    #
    cI
    wf1
    #
    @8
    vx
    cI
    cG
    cV
    usgrislfuspgr.v
    usgrislfuspgr.i
    usgrfs
    @12
    @2
    @11
    @7
    cI
    @2
    @11
    cI
    f1f
    @11
    @7
    wss
    @12
    @10
    @5
    vx
    @6
    @10
    @5
    wi
    @3
    @6
    wcel
    @10
    @5
    c2
    c2
    cle
    wbr
    #
    @13
    @10
    c2
    2re
    leidi
    a1i
    @4
    c2
    c2
    cle
    breq2
    mpbird
    a1i
    ss2rabi
    a1i
    fssd
    syl
    jca
    @9
    @0
    @2
    @10
    vx
    @6
    c0
    csn
    cdif
    #
    crab
    #
    cI
    wf1
    #
    @1
    @2
    @4
    c2
    cle
    wbr
    vx
    @14
    crab
    #
    cI
    wf1
    #
    @8
    @16
    vx
    cI
    cG
    cV
    usgrislfuspgr.v
    usgrislfuspgr.i
    uspgrf
    @18
    @8
    @16
    @18
    @2
    @17
    cI
    wf
    #
    cI
    ccnv
    wfun
    #
    wa
    @8
    @16
    wi
    @2
    @17
    cI
    df-f1
    @19
    @8
    @20
    @16
    @19
    @8
    wa
    #
    @20
    @16
    @21
    @20
    wa
    @2
    @15
    cI
    wf
    #
    @20
    wa
    @16
    @21
    @22
    @20
    @2
    @17
    @7
    cin
    #
    cI
    wf
    #
    @21
    @22
    @2
    @17
    @7
    cI
    fin
    @23
    @15
    wceq
    @24
    @22
    wb
    vx
    cV
    umgrislfupgrlem
    @23
    @15
    @2
    cI
    feq3
    ax-mp
    sylbb1
    anim1i
    @2
    @15
    cI
    df-f1
    sylibr
    ex
    impancom
    sylbi
    imp
    sylan
    @1
    @0
    @16
    wb
    @8
    vx
    cuspgr
    cI
    cG
    cV
    usgrislfuspgr.v
    usgrislfuspgr.i
    isusgr
    adantr
    mpbird
    impbii
end
