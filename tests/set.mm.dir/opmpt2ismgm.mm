include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cmpt2.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "ovmpt2elrn.mm"
include "syl3anc.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "wex.mm"
include "n0.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqcomi.mm"
include "ismgmn0.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "mpbird.mm"

theorem opmpt2ismgm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vk: setvar k
  assume opmpt2ismgm.b: |- B = ( Base ` M )
  assume opmpt2ismgm.p: |- ( +g ` M ) = ( x e. B , y e. B |-> C )
  assume opmpt2ismgm.n: |- ( ph -> B =/= (/) )
  assume opmpt2ismgm.c: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> C e. B )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint M x
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B b
  disjoint B e
  disjoint a b
  disjoint a e
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b x
  disjoint b y
  disjoint e x
  disjoint e y
  disjoint C a
  disjoint C b
  disjoint C e
  disjoint M a
  disjoint M b
  disjoint M e
  disjoint a ph
  disjoint b ph
  disjoint k x
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
    vx
    vy
    cB
    cB
    cC
    cmpt2
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
    cC
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
    @10
    @8
    wph
    @9
    vx
    vy
    cB
    cB
    opmpt2ismgm.c
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
    cC
    cB
    @3
    @1
    @2
    @3
    eqid
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
    opmpt2ismgm.n
    @11
    ve
    cv
    #
    cB
    wcel
    #
    ve
    wex
    @12
    ve
    cB
    n0
    @14
    @12
    ve
    va
    vb
    @13
    cB
    cM
    @3
    opmpt2ismgm.b
    cM
    cplusg
    cfv
    @3
    opmpt2ismgm.p
    eqcomi
    ismgmn0
    exlimiv
    sylbi
    syl
    mpbird
end
