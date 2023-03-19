include "cumgr.mm"
include "wcel.mm"
include "cupgr.mm"
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
include "umgrupgr.mm"
include "wceq.mm"
include "umgrf.mm"
include "id.mm"
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
include "upgrf.mm"
include "cin.mm"
include "fin.mm"
include "wb.mm"
include "umgrislfupgrlem.mm"
include "feq3.mm"
include "ax-mp.mm"
include "sylbb1.mm"
include "sylan.mm"
include "isumgr.mm"
include "adantr.mm"
include "impbii.mm"

theorem umgrislfupgr
  let vx: setvar x
  let cG: class G
  let cI: class I
  let cV: class V
  assume umgrislfupgr.v: |- V = ( Vtx ` G )
  assume umgrislfupgr.i: |- I = ( iEdg ` G )

  disjoint G x
  disjoint V x
  assert |- ( G e. UMGraph <-> ( G e. UPGraph /\ I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } ) )

  proof
    cG
    cumgr
    wcel
    #
    cG
    cupgr
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
    umgrupgr
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
    wf
    #
    @8
    vx
    cI
    cG
    cV
    umgrislfupgr.v
    umgrislfupgr.i
    umgrf
    @12
    @2
    @11
    @7
    cI
    @12
    id
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
    wf
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
    wf
    #
    @8
    @16
    vx
    cI
    cG
    cV
    umgrislfupgr.v
    umgrislfupgr.i
    upgrf
    @2
    @17
    @7
    cin
    #
    cI
    wf
    #
    @18
    @8
    wa
    @16
    @2
    @17
    @7
    cI
    fin
    @19
    @15
    wceq
    @20
    @16
    wb
    vx
    cV
    umgrislfupgrlem
    @19
    @15
    @2
    cI
    feq3
    ax-mp
    sylbb1
    sylan
    @1
    @0
    @16
    wb
    @8
    vx
    cupgr
    cI
    cG
    cV
    umgrislfupgr.v
    umgrislfupgr.i
    isumgr
    adantr
    mpbird
    impbii
end
