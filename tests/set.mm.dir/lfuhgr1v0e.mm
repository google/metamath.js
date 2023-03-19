include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cdm.mm"
include "wf.mm"
include "w3a.mm"
include "cedg.mm"
include "c0.mm"
include "ciedg.mm"
include "wa.mm"
include "a1i.mm"
include "dmeqi.mm"
include "c2.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "csn.mm"
include "wex.mm"
include "wi.mm"
include "cvv.mm"
include "wb.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "pweq.mm"
include "rabeqdv.mm"
include "wn.mm"
include "wral.mm"
include "cpr.mm"
include "cc0.mm"
include "clt.mm"
include "2pos.mm"
include "0re.mm"
include "2re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "1lt2.mm"
include "1re.mm"
include "0ex.mm"
include "snex.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "notbid.mm"
include "vex.mm"
include "hashsng.mm"
include "ralpr.mm"
include "mpbir2an.mm"
include "pwsn.mm"
include "raleqi.mm"
include "mpbir.mm"
include "rabeq0.mm"
include "a1d.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "impcom.mm"
include "syl5eq.mm"
include "feq123d.mm"
include "biimp3a.mm"
include "f00.mm"
include "simplbi.mm"
include "syl.mm"
include "uhgriedg0edg0.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem lfuhgr1v0e
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let vv: setvar v
  assume lfuhgr1v0e.v: |- V = ( Vtx ` G )
  assume lfuhgr1v0e.i: |- I = ( iEdg ` G )
  assume lfuhgr1v0e.e: |- E = { x e. ~P V | 2 <_ ( # ` x ) }

  disjoint G x
  disjoint V x
  disjoint G v
  disjoint v x
  disjoint V v
  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 1 /\ I : dom I --> E ) -> ( Edg ` G ) = (/) )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    chash
    cfv
    c1
    wceq
    #
    cI
    cdm
    #
    cE
    cI
    wf
    #
    w3a
    #
    cG
    cedg
    cfv
    c0
    wceq
    #
    cG
    ciedg
    cfv
    #
    c0
    wceq
    #
    @4
    @6
    cdm
    #
    c0
    @6
    wf
    #
    @7
    @0
    @1
    @3
    @9
    @0
    @1
    wa
    #
    @2
    @8
    cE
    c0
    cI
    @6
    cI
    @6
    wceq
    @10
    lfuhgr1v0e.i
    a1i
    @2
    @8
    wceq
    @10
    cI
    @6
    lfuhgr1v0e.i
    dmeqi
    a1i
    @10
    cE
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
    c0
    lfuhgr1v0e.e
    @1
    @0
    @15
    c0
    wceq
    #
    @1
    cV
    vv
    cv
    #
    csn
    #
    wceq
    #
    vv
    wex
    #
    @0
    @16
    wi
    #
    cV
    cvv
    wcel
    @1
    @20
    wb
    cV
    cG
    cvtx
    cfv
    cvv
    lfuhgr1v0e.v
    cG
    cvtx
    fvex
    eqeltri
    cV
    cvv
    vv
    hash1snb
    ax-mp
    @19
    @21
    vv
    @19
    @16
    @0
    @19
    @15
    @13
    vx
    @18
    cpw
    #
    crab
    #
    c0
    @19
    @13
    vx
    @14
    @22
    cV
    @18
    pweq
    rabeqdv
    @23
    c0
    wceq
    @13
    wn
    #
    vx
    @22
    wral
    #
    @25
    @24
    vx
    c0
    @18
    cpr
    #
    wral
    #
    @27
    c2
    cc0
    cle
    wbr
    #
    wn
    #
    c2
    c1
    cle
    wbr
    #
    wn
    #
    cc0
    c2
    clt
    wbr
    @29
    2pos
    cc0
    c2
    0re
    2re
    ltnlei
    mpbi
    c1
    c2
    clt
    wbr
    @31
    1lt2
    c1
    c2
    1re
    2re
    ltnlei
    mpbi
    @24
    @29
    @31
    vx
    c0
    @18
    0ex
    @17
    snex
    @11
    c0
    wceq
    #
    @13
    @28
    @32
    @12
    cc0
    c2
    cle
    @32
    @12
    c0
    chash
    cfv
    cc0
    @11
    c0
    chash
    fveq2
    hash0
    syl6eq
    breq2d
    notbid
    @11
    @18
    wceq
    #
    @13
    @30
    @33
    @12
    c1
    c2
    cle
    @33
    @12
    @18
    chash
    cfv
    #
    c1
    @11
    @18
    chash
    fveq2
    @17
    cvv
    wcel
    @34
    c1
    wceq
    vv
    vex
    @17
    cvv
    hashsng
    ax-mp
    syl6eq
    breq2d
    notbid
    ralpr
    mpbir2an
    @24
    vx
    @22
    @26
    @17
    pwsn
    raleqi
    mpbir
    @13
    vx
    @22
    rabeq0
    mpbir
    syl6eq
    a1d
    exlimiv
    sylbi
    impcom
    syl5eq
    feq123d
    biimp3a
    @9
    @7
    @8
    c0
    wceq
    @8
    @6
    f00
    simplbi
    syl
    @0
    @1
    @5
    @7
    wb
    @3
    cG
    uhgriedg0edg0
    3ad2ant1
    mpbird
end
