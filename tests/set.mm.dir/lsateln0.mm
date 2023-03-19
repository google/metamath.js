include "cv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wne.mm"
include "clspn.mm"
include "wceq.mm"
include "clmod.mm"
include "wb.mm"
include "eqid.mm"
include "islsat.mm"
include "syl.mm"
include "mpbid.mm"
include "wa.mm"
include "eldifi.mm"
include "lspsnid.mm"
include "syl2an.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "reximdva.mm"
include "mpd.mm"
include "eldifsn.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "simprbi.mm"
include "ancomd.mm"
include "reximi2.mm"

theorem lsateln0
  let wph: wff ph
  let vv: setvar v
  let cA: class A
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsateln0.z: |- .0. = ( 0g ` W )
  assume lsateln0.a: |- A = ( LSAtoms ` W )
  assume lsateln0.w: |- ( ph -> W e. LMod )
  assume lsateln0.u: |- ( ph -> U e. A )

  disjoint U v
  disjoint W v
  disjoint .0. v
  disjoint ph v
  assert |- ( ph -> E. v e. U v =/= .0. )

  proof
    wph
    vv
    cv
    #
    cU
    wcel
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
    @0
    c.0
    wne
    #
    vv
    cU
    wrex
    wph
    cU
    @0
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
    @4
    wrex
    #
    @5
    wph
    cU
    cA
    wcel
    #
    @10
    lsateln0.u
    wph
    cW
    clmod
    wcel
    #
    @11
    @10
    wb
    lsateln0.w
    vv
    cA
    cU
    @7
    @2
    cW
    clmod
    c.0
    @2
    eqid
    #
    @7
    eqid
    #
    lsateln0.z
    lsateln0.a
    islsat
    syl
    mpbid
    wph
    @9
    @1
    vv
    @4
    wph
    @0
    @4
    wcel
    #
    wa
    @1
    @9
    @0
    @8
    wcel
    #
    wph
    @12
    @0
    @2
    wcel
    #
    @16
    @15
    lsateln0.w
    @0
    @2
    @3
    eldifi
    @7
    @2
    cW
    @0
    @13
    @14
    lspsnid
    syl2an
    cU
    @8
    @0
    eleq2
    syl5ibrcom
    reximdva
    mpd
    @1
    @6
    vv
    @4
    cU
    @15
    @1
    wa
    #
    @6
    @1
    @18
    @17
    @6
    @1
    wa
    #
    @18
    @17
    @6
    wa
    #
    @1
    wa
    @17
    @19
    wa
    @15
    @20
    @1
    @0
    @2
    c.0
    eldifsn
    anbi1i
    @17
    @6
    @1
    anass
    bitri
    simprbi
    ancomd
    reximi2
    syl
end
