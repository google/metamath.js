include "cv.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wral.mm"
include "cph.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "cva.mm"
include "wrex.mm"
include "chil.mm"
include "chshii.mm"
include "shjcli.mm"
include "cheli.mm"
include "pjcli.mm"
include "anim1i.mm"
include "cch.mm"
include "axpjpj.mm"
include "mpan.mm"
include "adantr.mm"
include "jca.mm"
include "sylan.mm"
include "rspceov.mm"
include "3expa.mm"
include "syl.mm"
include "shseli.mm"
include "sylibr.mm"
include "ex.mm"
include "syldc.mm"
include "ssrdv.mm"
include "shsleji.mm"
include "jctir.mm"
include "eqss.mm"

theorem pjjsi
  let vx: setvar x
  let cG: class G
  let cH: class H
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume pjjs.1: |- G e. CH
  assume pjjs.2: |- H e. SH

  disjoint G x
  disjoint H x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint G y
  disjoint w z
  disjoint G z
  disjoint G w
  disjoint H y
  disjoint H z
  disjoint H w
  assert |- ( A. x e. ( G vH H ) ( ( projh ` ( _|_ ` G ) ) ` x ) e. H -> ( G vH H ) = ( G +H H ) )

  proof
    vx
    cv
    #
    cG
    cort
    cfv
    cpjh
    cfv
    #
    cfv
    #
    cH
    wcel
    #
    vx
    cG
    cH
    chj
    co
    #
    wral
    #
    @4
    cG
    cH
    cph
    co
    #
    wss
    #
    @6
    @4
    wss
    #
    wa
    @4
    @6
    wceq
    @5
    @7
    @8
    @5
    vw
    @4
    @6
    vw
    cv
    #
    @4
    wcel
    #
    @5
    @9
    @1
    cfv
    #
    cH
    wcel
    #
    @9
    @6
    wcel
    #
    @3
    @12
    vx
    @9
    @4
    @0
    @9
    wceq
    @2
    @11
    cH
    @0
    @9
    @1
    fveq2
    eleq1d
    rspcv
    @10
    @12
    @13
    @10
    @12
    wa
    #
    @9
    vy
    cv
    vz
    cv
    cva
    co
    wceq
    vz
    cH
    wrex
    vy
    cG
    wrex
    #
    @13
    @14
    @9
    cG
    cpjh
    cfv
    cfv
    #
    cG
    wcel
    #
    @12
    wa
    #
    @9
    @16
    @11
    cva
    co
    wceq
    #
    wa
    #
    @15
    @10
    @9
    chil
    wcel
    #
    @12
    @20
    @9
    @4
    cG
    cH
    cG
    pjjs.1
    chshii
    #
    pjjs.2
    shjcli
    cheli
    @21
    @12
    wa
    @18
    @19
    @21
    @17
    @12
    @9
    cG
    pjjs.1
    pjcli
    anim1i
    @21
    @19
    @12
    cG
    cch
    wcel
    @21
    @19
    pjjs.1
    @9
    cG
    axpjpj
    mpan
    adantr
    jca
    sylan
    @17
    @12
    @19
    @15
    vy
    vz
    cG
    cH
    @16
    @11
    @9
    cva
    rspceov
    3expa
    syl
    vy
    vz
    cG
    cH
    @9
    @22
    pjjs.2
    shseli
    sylibr
    ex
    syldc
    ssrdv
    cG
    cH
    @22
    pjjs.2
    shsleji
    jctir
    @4
    @6
    eqss
    sylibr
end
