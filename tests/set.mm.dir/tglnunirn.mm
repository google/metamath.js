include "cstrkg.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "crn.mm"
include "wral.mm"
include "cuni.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "tglng.mm"
include "rneqd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "elrnmpt2.mm"
include "ssrab2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "syl.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "sylibr.mm"

theorem tglnunirn
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglng.p: |- P = ( Base ` G )
  assume tglng.l: |- L = ( LineG ` G )
  assume tglng.i: |- I = ( Itv ` G )


  assert |- ( G e. TarskiG -> U. ran L C_ P )

  proof
    cG
    cstrkg
    wcel
    #
    vp
    cv
    #
    cP
    wss
    #
    vp
    cL
    crn
    #
    wral
    @3
    cuni
    cP
    wss
    @0
    @2
    vp
    @3
    @0
    @1
    @3
    wcel
    #
    wa
    @1
    vx
    vy
    cP
    cP
    vx
    cv
    #
    csn
    cdif
    #
    vz
    cv
    #
    @5
    vy
    cv
    #
    cI
    co
    wcel
    @5
    @7
    @8
    cI
    co
    wcel
    @8
    @5
    @7
    cI
    co
    wcel
    w3o
    #
    vz
    cP
    crab
    #
    cmpt2
    #
    crn
    #
    wcel
    #
    @2
    @0
    @4
    @13
    @0
    @3
    @12
    @1
    @0
    cL
    @11
    vx
    vy
    vz
    cP
    cG
    cI
    cL
    tglng.p
    tglng.l
    tglng.i
    tglng
    rneqd
    eleq2d
    biimpa
    @13
    @1
    @10
    wceq
    #
    vy
    @6
    wrex
    #
    vx
    cP
    wrex
    @2
    vx
    vy
    cP
    @6
    @10
    @1
    @11
    @11
    eqid
    @9
    vz
    cP
    cP
    cG
    cbs
    cfv
    cvv
    tglng.p
    cG
    cbs
    fvex
    eqeltri
    rabex
    elrnmpt2
    @15
    @2
    vx
    cP
    @14
    @2
    vy
    @6
    @14
    @2
    @10
    cP
    wss
    @9
    vz
    cP
    ssrab2
    @1
    @10
    cP
    sseq1
    mpbiri
    rexlimivw
    rexlimivw
    sylbi
    syl
    ralrimiva
    vp
    @3
    cP
    unissb
    sylibr
end
