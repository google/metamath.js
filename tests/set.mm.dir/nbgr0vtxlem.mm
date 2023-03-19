include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "eqid.mm"
include "nbgrval.mm"
include "ad2antrl.mm"
include "wn.mm"
include "wral.mm"
include "ad2antll.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "expcom.mm"
include "ex.mm"
include "com23.mm"
include "wnel.mm"
include "df-nel.mm"
include "nbgrnvtx0.mm"
include "sylbir.mm"
include "a1d.mm"
include "nbgrprc0.mm"
include "pm2.61nii.mm"

theorem nbgr0vtxlem
  let wph: wff ph
  let ve: setvar e
  let vn: setvar n
  let cG: class G
  let cK: class K
  assume nbgr0vtxlem.v: |- ( ph -> A. n e. ( ( Vtx ` G ) \ { K } ) -. E. e e. ( Edg ` G ) { K , n } C_ e )

  disjoint G e
  disjoint G n
  disjoint e n
  disjoint K e
  disjoint K n
  assert |- ( ph -> ( G NeighbVtx K ) = (/) )

  proof
    cK
    cG
    cvtx
    cfv
    #
    wcel
    #
    cG
    cvv
    wcel
    cK
    cvv
    wcel
    wa
    #
    wph
    cG
    cK
    cnbgr
    co
    #
    c0
    wceq
    #
    wi
    @1
    wph
    @2
    @4
    @1
    wph
    @2
    @4
    wi
    @2
    @1
    wph
    wa
    #
    @4
    @2
    @5
    wa
    #
    @3
    cK
    vn
    cv
    cpr
    ve
    cv
    wss
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    vn
    @0
    cK
    csn
    cdif
    #
    crab
    #
    c0
    @1
    @3
    @10
    wceq
    @2
    wph
    ve
    vn
    @7
    cG
    cK
    @0
    @0
    eqid
    #
    @7
    eqid
    nbgrval
    ad2antrl
    @6
    @8
    wn
    vn
    @9
    wral
    #
    @10
    c0
    wceq
    wph
    @12
    @2
    @1
    nbgr0vtxlem.v
    ad2antll
    @8
    vn
    @9
    rabeq0
    sylibr
    eqtrd
    expcom
    ex
    com23
    @1
    wn
    #
    @4
    wph
    @13
    cK
    @0
    wnel
    @4
    cK
    @0
    df-nel
    cG
    @0
    cK
    @11
    nbgrnvtx0
    sylbir
    a1d
    @2
    wn
    @4
    wph
    cG
    cK
    nbgrprc0
    a1d
    pm2.61nii
end
