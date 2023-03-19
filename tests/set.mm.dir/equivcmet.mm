include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cmopn.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccfil.mm"
include "wral.mm"
include "wa.mm"
include "cms.mm"
include "2thd.mm"
include "equivcfil.mm"
include "eqssd.mm"
include "eqid.mm"
include "metss2.mm"
include "oveq1d.mm"
include "neeq1d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "iscmet.mm"
include "3bitr4g.mm"

theorem equivcmet
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cX: class X
  let vf: setvar f
  assume equivcmet.1: |- ( ph -> C e. ( Met ` X ) )
  assume equivcmet.2: |- ( ph -> D e. ( Met ` X ) )
  assume equivcmet.3: |- ( ph -> R e. RR+ )
  assume equivcmet.4: |- ( ph -> S e. RR+ )
  assume equivcmet.5: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x C y ) <_ ( R x. ( x D y ) ) )
  assume equivcmet.6: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x D y ) <_ ( S x. ( x C y ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint S x
  disjoint S y
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint D f
  disjoint f ph
  disjoint X f
  assert |- ( ph -> ( C e. ( CMet ` X ) <-> D e. ( CMet ` X ) ) )

  proof
    wph
    cC
    cX
    cme
    cfv
    #
    wcel
    #
    cC
    cmopn
    cfv
    #
    vf
    cv
    #
    cflim
    co
    #
    c0
    wne
    #
    vf
    cC
    ccfil
    cfv
    #
    wral
    #
    wa
    cD
    @0
    wcel
    #
    cD
    cmopn
    cfv
    #
    @3
    cflim
    co
    #
    c0
    wne
    #
    vf
    cD
    ccfil
    cfv
    #
    wral
    #
    wa
    cC
    cX
    cms
    cfv
    #
    wcel
    cD
    @14
    wcel
    wph
    @1
    @8
    @7
    @13
    wph
    @1
    @8
    equivcmet.1
    equivcmet.2
    2thd
    wph
    @5
    @11
    vf
    @6
    @12
    wph
    @6
    @12
    wph
    vx
    vy
    cD
    cC
    cS
    cX
    equivcmet.2
    equivcmet.1
    equivcmet.4
    equivcmet.6
    equivcfil
    wph
    vx
    vy
    cC
    cD
    cR
    cX
    equivcmet.1
    equivcmet.2
    equivcmet.3
    equivcmet.5
    equivcfil
    eqssd
    wph
    @4
    @10
    c0
    wph
    @2
    @9
    @3
    cflim
    wph
    @2
    @9
    wph
    vx
    vy
    cC
    cD
    cR
    @2
    @9
    cX
    @2
    eqid
    #
    @9
    eqid
    #
    equivcmet.1
    equivcmet.2
    equivcmet.3
    equivcmet.5
    metss2
    wph
    vx
    vy
    cD
    cC
    cS
    @9
    @2
    cX
    @16
    @15
    equivcmet.2
    equivcmet.1
    equivcmet.4
    equivcmet.6
    metss2
    eqssd
    oveq1d
    neeq1d
    raleqbidv
    anbi12d
    cC
    vf
    @2
    cX
    @15
    iscmet
    cD
    vf
    @9
    cX
    @16
    iscmet
    3bitr4g
end
