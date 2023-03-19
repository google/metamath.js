include "cfv.mm"
include "cestrc.mm"
include "crngh.mm"
include "crng.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "co.mm"
include "ccid.mm"
include "cid.mm"
include "eqidd.mm"
include "rngcval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "eqid.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "rnghmsubcsetc.mm"
include "rnghmresfn.mm"
include "wcel.mm"
include "rngcbas.mm"
include "eleq2d.mm"
include "mpbid.mm"
include "subcid.mm"
include "cbs.mm"
include "elinel1.mm"
include "syl6bi.mm"
include "mpd.mm"
include "estrcid.mm"
include "eqcomi.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"

theorem rngcid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume rngccat.c: |- C = ( RngCat ` U )
  assume rngcid.b: |- B = ( Base ` C )
  assume rngcid.o: |- .1. = ( Id ` C )
  assume rngcid.u: |- ( ph -> U e. V )
  assume rngcid.x: |- ( ph -> X e. B )
  assume rngcid.s: |- S = ( Base ` X )


  assert |- ( ph -> ( .1. ` X ) = ( _I |` S ) )

  proof
    wph
    cX
    c.1
    cfv
    cX
    cU
    cestrc
    cfv
    #
    crngh
    cU
    crng
    cin
    #
    @1
    cxp
    cres
    #
    cresc
    co
    #
    ccid
    cfv
    #
    cfv
    cX
    @0
    ccid
    cfv
    #
    cfv
    #
    cid
    cS
    cres
    #
    wph
    cX
    c.1
    @4
    wph
    c.1
    cC
    ccid
    cfv
    @4
    rngcid.o
    wph
    cC
    @3
    ccid
    wph
    @1
    cC
    cU
    @2
    cV
    rngccat.c
    rngcid.u
    wph
    @1
    eqidd
    #
    wph
    @2
    eqidd
    #
    rngcval
    fveq2d
    syl5eq
    fveq1d
    wph
    @0
    @3
    @1
    @5
    @2
    cX
    @3
    eqid
    wph
    @1
    @0
    cU
    @2
    cV
    @0
    eqid
    #
    rngcid.u
    @1
    crng
    cU
    cin
    wceq
    wph
    cU
    crng
    incom
    a1i
    @9
    rnghmsubcsetc
    wph
    @1
    cU
    @2
    @8
    @9
    rnghmresfn
    @5
    eqid
    #
    wph
    cX
    cB
    wcel
    #
    cX
    @1
    wcel
    #
    rngcid.x
    wph
    cB
    @1
    cX
    wph
    cB
    cC
    cU
    cV
    rngccat.c
    rngcid.b
    rngcid.u
    rngcbas
    eleq2d
    #
    mpbid
    subcid
    wph
    @6
    cid
    cX
    cbs
    cfv
    #
    cres
    @7
    wph
    @0
    cU
    @5
    cV
    cX
    @10
    @11
    rngcid.u
    wph
    @12
    cX
    cU
    wcel
    #
    rngcid.x
    wph
    @12
    @13
    @16
    @14
    cX
    cU
    crng
    elinel1
    syl6bi
    mpd
    estrcid
    wph
    @15
    cS
    cid
    @15
    cS
    wceq
    wph
    cS
    @15
    rngcid.s
    eqcomi
    a1i
    reseq2d
    eqtrd
    3eqtr2d
end
