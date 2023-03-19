include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "clinds.mm"
include "wceq.mm"
include "eqid.mm"
include "lssss.mm"
include "ressbas2.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "sseq2d.mm"
include "sstr2.mm"
include "mpan9.mm"
include "simpl3.mm"
include "impbida.mm"
include "bitr3d.mm"
include "crn.mm"
include "wb.mm"
include "rnresi.mm"
include "sseq1i.mm"
include "lsslindf.mm"
include "syl3an3br.mm"
include "anbi12d.mm"
include "cvv.mm"
include "cress.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "islinds.mm"
include "mp1i.mm"
include "3ad2ant1.mm"
include "3bitr4d.mm"

theorem lsslinds
  let cS: class S
  let cU: class U
  let cF: class F
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume lsslindf.u: |- U = ( LSubSp ` W )
  assume lsslindf.x: |- X = ( W |`s S )


  assert |- ( ( W e. LMod /\ S e. U /\ F C_ S ) -> ( F e. ( LIndS ` X ) <-> F e. ( LIndS ` W ) ) )

  proof
    cW
    clmod
    wcel
    #
    cS
    cU
    wcel
    #
    cF
    cS
    wss
    #
    w3a
    #
    cF
    cX
    cbs
    cfv
    #
    wss
    #
    cid
    cF
    cres
    #
    cX
    clindf
    wbr
    #
    wa
    #
    cF
    cW
    cbs
    cfv
    #
    wss
    #
    @6
    cW
    clindf
    wbr
    #
    wa
    #
    cF
    cX
    clinds
    cfv
    wcel
    #
    cF
    cW
    clinds
    cfv
    wcel
    #
    @3
    @5
    @10
    @7
    @11
    @3
    @2
    @5
    @10
    @3
    cS
    @4
    cF
    @1
    @0
    cS
    @4
    wceq
    #
    @2
    @1
    cS
    @9
    wss
    #
    @15
    cU
    cS
    @9
    cW
    @9
    eqid
    #
    lsslindf.u
    lssss
    #
    cS
    @9
    cX
    cW
    lsslindf.x
    @17
    ressbas2
    syl
    3ad2ant2
    sseq2d
    @3
    @2
    @10
    @3
    @16
    @2
    @10
    @1
    @0
    @16
    @2
    @18
    3ad2ant2
    cF
    cS
    @9
    sstr2
    mpan9
    @0
    @1
    @2
    @10
    simpl3
    impbida
    bitr3d
    @2
    @0
    @1
    @6
    crn
    #
    cS
    wss
    @7
    @11
    wb
    @19
    cF
    cS
    cF
    rnresi
    sseq1i
    cS
    cU
    @6
    cW
    cX
    lsslindf.u
    lsslindf.x
    lsslindf
    syl3an3br
    anbi12d
    cX
    cvv
    wcel
    @13
    @8
    wb
    @3
    cX
    cW
    cS
    cress
    co
    cvv
    lsslindf.x
    cW
    cS
    cress
    ovex
    eqeltri
    @4
    cvv
    cX
    cF
    @4
    eqid
    islinds
    mp1i
    @0
    @1
    @14
    @12
    wb
    @2
    @9
    clmod
    cW
    cF
    @17
    islinds
    3ad2ant1
    3bitr4d
end
