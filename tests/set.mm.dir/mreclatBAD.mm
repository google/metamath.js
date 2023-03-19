include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpo.mm"
include "cv.mm"
include "cbs.mm"
include "wss.mm"
include "club.mm"
include "cglb.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "ccla.mm"
include "ipopos.mm"
include "a1i.mm"
include "cuni.mm"
include "cmrc.mm"
include "eqid.mm"
include "mrelatlub.mm"
include "uniss.mm"
include "adantl.mm"
include "wceq.mm"
include "mreuni.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "mrccl.mm"
include "syldan.mm"
include "eqeltrd.mm"
include "c0.mm"
include "fveq2.mm"
include "mrelatglb0.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "mre1cl.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "mrelatglb.mm"
include "mreintcl.mm"
include "3expa.mm"
include "pm2.61dane.mm"
include "jca.mm"
include "ex.mm"
include "wb.mm"
include "ipobas.mm"
include "sseq2.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "syl.mm"
include "mpbid.mm"
include "alrimiv.mm"
include "sylanbrc.mm"

theorem mreclatBAD
  let vx: setvar x
  let cC: class C
  let cI: class I
  let cX: class X
  let vy: setvar y
  let cG: class G
  let cL: class L
  let cU: class U
  let cF: class F
  assume mreclat.i: |- I = ( toInc ` C )
  assume isclatBAD.: |- ( I e. CLat <-> ( I e. Poset /\ A. x ( x C_ ( Base ` I ) -> ( ( ( lub ` I ) ` x ) e. ( Base ` I ) /\ ( ( glb ` I ) ` x ) e. ( Base ` I ) ) ) ) )

  disjoint I x
  disjoint C x
  disjoint X x
  disjoint I y
  disjoint x y
  disjoint C y
  disjoint G x
  disjoint G y
  disjoint L x
  disjoint L y
  disjoint U x
  disjoint U y
  disjoint F x
  disjoint F y
  disjoint X y
  assert |- ( C e. ( Moore ` X ) -> I e. CLat )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cI
    cpo
    wcel
    #
    vx
    cv
    #
    cI
    cbs
    cfv
    #
    wss
    #
    @3
    cI
    club
    cfv
    #
    cfv
    #
    @4
    wcel
    #
    @3
    cI
    cglb
    cfv
    #
    cfv
    #
    @4
    wcel
    #
    wa
    #
    wi
    #
    vx
    wal
    cI
    ccla
    wcel
    @2
    @1
    cC
    cI
    mreclat.i
    ipopos
    a1i
    @1
    @13
    vx
    @1
    @3
    cC
    wss
    #
    @7
    cC
    wcel
    #
    @10
    cC
    wcel
    #
    wa
    #
    wi
    #
    @13
    @1
    @14
    @17
    @1
    @14
    wa
    #
    @15
    @16
    @19
    @7
    @3
    cuni
    #
    cC
    cmrc
    cfv
    #
    cfv
    #
    cC
    cC
    @3
    @21
    cI
    @6
    cX
    mreclat.i
    @21
    eqid
    #
    @6
    eqid
    mrelatlub
    @1
    @14
    @20
    cX
    wss
    @22
    cC
    wcel
    @19
    @20
    cC
    cuni
    #
    cX
    @14
    @20
    @24
    wss
    @1
    @3
    cC
    uniss
    adantl
    @1
    @24
    cX
    wceq
    @14
    cC
    cX
    mreuni
    adantr
    sseqtrd
    cC
    @20
    @21
    cX
    @23
    mrccl
    syldan
    eqeltrd
    @19
    @16
    @3
    c0
    @19
    @3
    c0
    wceq
    #
    wa
    #
    @10
    cX
    cC
    @26
    @10
    c0
    @9
    cfv
    #
    cX
    @25
    @10
    @27
    wceq
    @19
    @3
    c0
    @9
    fveq2
    adantl
    @1
    @27
    cX
    wceq
    @14
    @25
    cC
    @9
    cI
    cX
    mreclat.i
    @9
    eqid
    #
    mrelatglb0
    ad2antrr
    eqtrd
    @1
    cX
    cC
    wcel
    @14
    @25
    cC
    cX
    mre1cl
    ad2antrr
    eqeltrd
    @1
    @14
    @3
    c0
    wne
    #
    @16
    @1
    @14
    @29
    w3a
    @10
    @3
    cint
    cC
    cC
    @3
    @9
    cI
    cX
    mreclat.i
    @28
    mrelatglb
    cC
    @3
    cX
    mreintcl
    eqeltrd
    3expa
    pm2.61dane
    jca
    ex
    @1
    cC
    @4
    wceq
    #
    @18
    @13
    wb
    cC
    cI
    @0
    mreclat.i
    ipobas
    @30
    @14
    @5
    @17
    @12
    cC
    @4
    @3
    sseq2
    @30
    @15
    @8
    @16
    @11
    cC
    @4
    @7
    eleq2
    cC
    @4
    @10
    eleq2
    anbi12d
    imbi12d
    syl
    mpbid
    alrimiv
    isclatBAD.
    sylanbrc
end
