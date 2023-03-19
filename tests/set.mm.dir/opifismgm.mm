include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cif.mm"
include "ifcld.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "ovmpt2elrn.mm"
include "syl3anc.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "wex.mm"
include "n0.mm"
include "eqid.mm"
include "ismgmn0.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "mpbird.mm"

theorem opifismgm
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let va: setvar a
  let vb: setvar b
  assume opifismgm.b: |- B = ( Base ` M )
  assume opifismgm.p: |- ( +g ` M ) = ( x e. B , y e. B |-> if ( ps , C , D ) )
  assume opifismgm.n: |- ( ph -> B =/= (/) )
  assume opifismgm.c: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> C e. B )
  assume opifismgm.d: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> D e. B )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint M x
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint M a
  disjoint M b
  disjoint a x
  disjoint b x
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> M e. Mgm )

  proof
    wph
    cM
    cmgm
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    cB
    wcel
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wph
    @4
    va
    vb
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    wa
    wps
    cC
    cD
    cif
    #
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @6
    @7
    @4
    wph
    @11
    @8
    wph
    @10
    vx
    vy
    cB
    cB
    wph
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    cB
    wcel
    wa
    wa
    wps
    cC
    cD
    cB
    opifismgm.c
    opifismgm.d
    ifcld
    ralrimivva
    adantr
    wph
    @6
    @7
    simprl
    wph
    @6
    @7
    simprr
    vx
    vy
    cB
    cB
    @9
    cB
    @3
    @1
    @2
    opifismgm.p
    ovmpt2elrn
    syl3anc
    ralrimivva
    wph
    cB
    c0
    wne
    #
    @0
    @5
    wb
    #
    opifismgm.n
    @14
    @13
    vx
    wex
    @15
    vx
    cB
    n0
    @13
    @15
    vx
    va
    vb
    @12
    cB
    cM
    @3
    opifismgm.b
    @3
    eqid
    ismgmn0
    exlimiv
    sylbi
    syl
    mpbird
end
