include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cdif.mm"
include "wrex.mm"
include "wne.mm"
include "wcel.mm"
include "clmod.mm"
include "wb.mm"
include "eqid.mm"
include "islsat.mm"
include "syl.mm"
include "mpbid.mm"
include "wi.mm"
include "wa.mm"
include "eldifsn.mm"
include "lspsneq0.mm"
include "sylan.mm"
include "biimpd.mm"
include "necon3d.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "neeq1.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem lsatn0
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cW: class W
  let c.0: class .0.
  let vv: setvar v
  assume lsatn0.o: |- .0. = ( 0g ` W )
  assume lsatn0.a: |- A = ( LSAtoms ` W )
  assume lsatn0.w: |- ( ph -> W e. LMod )
  assume lsatn0.u: |- ( ph -> U e. A )


  assert |- ( ph -> U =/= { .0. } )

  proof
    wph
    cU
    vv
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vv
    cW
    cbs
    cfv
    #
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    cU
    @5
    wne
    #
    wph
    cU
    cA
    wcel
    #
    @7
    lsatn0.u
    wph
    cW
    clmod
    wcel
    #
    @9
    @7
    wb
    lsatn0.w
    vv
    cA
    cU
    @1
    @4
    cW
    clmod
    c.0
    @4
    eqid
    #
    @1
    eqid
    #
    lsatn0.o
    lsatn0.a
    islsat
    syl
    mpbid
    wph
    @3
    @8
    vv
    @6
    wph
    @0
    @6
    wcel
    #
    @2
    @5
    wne
    #
    @3
    @8
    wi
    @13
    @0
    @4
    wcel
    #
    @0
    c.0
    wne
    #
    wa
    wph
    @14
    @0
    @4
    c.0
    eldifsn
    wph
    @15
    @16
    @14
    wph
    @15
    wa
    #
    @2
    @5
    @0
    c.0
    @17
    @2
    @5
    wceq
    #
    @0
    c.0
    wceq
    #
    wph
    @10
    @15
    @18
    @19
    wb
    lsatn0.w
    @1
    @4
    cW
    @0
    c.0
    @11
    lsatn0.o
    @12
    lspsneq0
    sylan
    biimpd
    necon3d
    expimpd
    syl5bi
    @3
    @8
    @14
    cU
    @2
    @5
    neeq1
    biimprcd
    syl6
    rexlimdv
    mpd
end
