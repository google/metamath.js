include "cv.mm"
include "cmpt2.mm"
include "co.mm"
include "wne.mm"
include "wrex.mm"
include "wral.mm"
include "cmnd.mm"
include "wnel.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simpr.mm"
include "simpl.mm"
include "hashgt12el2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "eqidd.mm"
include "weq.mm"
include "adantr.mm"
include "ovmpt2d.mm"
include "eqtr3d.mm"
include "ex.mm"
include "ralimdva.mm"
include "rexlimdva.mm"
include "con3d.mm"
include "bicomi.mm"
include "ralbii.mm"
include "ralnex.mm"
include "3bitr3i.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "syl5.mm"
include "mp2and.mm"
include "cplusg.mm"
include "eqcomi.mm"
include "isnmnd.mm"
include "syl.mm"

theorem copisnmnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cM: class M
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  assume copisnmnd.b: |- B = ( Base ` M )
  assume copisnmnd.p: |- ( +g ` M ) = ( x e. B , y e. B |-> C )
  assume copisnmnd.c: |- ( ph -> C e. B )
  assume copisnmnd.n: |- ( ph -> 1 < ( # ` B ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B c
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint c x
  disjoint c y
  disjoint C a
  disjoint C c
  disjoint M a
  disjoint M c
  disjoint a ph
  disjoint c ph
  disjoint k x
  assert |- ( ph -> M e/ Mnd )

  proof
    wph
    va
    cv
    #
    vc
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
    #
    @1
    wne
    #
    vc
    cB
    wrex
    #
    va
    cB
    wral
    #
    cM
    cmnd
    wnel
    wph
    cC
    cB
    wcel
    #
    c1
    cB
    chash
    cfv
    clt
    wbr
    #
    @6
    copisnmnd.c
    copisnmnd.n
    @7
    @8
    wa
    #
    cC
    @1
    wne
    #
    vc
    cB
    wrex
    #
    wph
    @6
    @9
    cB
    cvv
    wcel
    #
    @8
    @7
    @11
    @12
    @9
    cB
    cM
    cbs
    cfv
    cvv
    copisnmnd.b
    cM
    cbs
    fvex
    eqeltri
    a1i
    @7
    @8
    simpr
    @7
    @8
    simpl
    cC
    cB
    cvv
    vc
    hashgt12el2
    syl3anc
    @11
    cC
    @1
    wceq
    #
    vc
    cB
    wral
    #
    wn
    #
    wph
    @6
    @11
    @13
    wn
    #
    vc
    cB
    wrex
    @15
    @10
    @16
    vc
    cB
    cC
    @1
    df-ne
    rexbii
    @13
    vc
    cB
    rexnal
    bitri
    wph
    @15
    @3
    @1
    wceq
    #
    vc
    cB
    wral
    #
    va
    cB
    wrex
    #
    wn
    #
    @6
    wph
    @19
    @14
    wph
    @18
    @14
    va
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @17
    @13
    vc
    cB
    @22
    @1
    cB
    wcel
    #
    wa
    #
    @17
    @13
    @24
    @17
    wa
    @3
    cC
    @1
    @24
    @3
    cC
    wceq
    @17
    @24
    vx
    vy
    @0
    @1
    cB
    cB
    cC
    cC
    @2
    cB
    @24
    @2
    eqidd
    @24
    vx
    va
    weq
    vy
    vc
    weq
    wa
    wa
    cC
    eqidd
    @22
    @21
    @23
    wph
    @21
    simpr
    adantr
    @22
    @23
    simpr
    @22
    @7
    @23
    wph
    @7
    @21
    copisnmnd.c
    adantr
    adantr
    ovmpt2d
    adantr
    @24
    @17
    simpr
    eqtr3d
    ex
    ralimdva
    rexlimdva
    con3d
    @18
    wn
    #
    va
    cB
    wral
    @17
    wn
    #
    vc
    cB
    wrex
    #
    va
    cB
    wral
    @20
    @6
    @25
    @27
    va
    cB
    @27
    @25
    @17
    vc
    cB
    rexnal
    bicomi
    ralbii
    @18
    va
    cB
    ralnex
    @27
    @5
    va
    cB
    @26
    @4
    vc
    cB
    @4
    @26
    @3
    @1
    df-ne
    bicomi
    rexbii
    ralbii
    3bitr3i
    syl6ib
    syl5bi
    syl5
    mp2and
    vc
    va
    cB
    cM
    @2
    copisnmnd.b
    cM
    cplusg
    cfv
    @2
    copisnmnd.p
    eqcomi
    isnmnd
    syl
end
