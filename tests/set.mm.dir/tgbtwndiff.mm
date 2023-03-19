include "cv.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "axtgsegcon.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "axtgcgrid.mm"
include "simp-4r.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "ex.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "tglowdim1.mm"
include "r19.29vva.mm"

theorem tgbtwndiff
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  assume tgbtwndiff.p: |- P = ( Base ` G )
  assume tgbtwndiff.d: |- .- = ( dist ` G )
  assume tgbtwndiff.i: |- I = ( Itv ` G )
  assume tgbtwndiff.g: |- ( ph -> G e. TarskiG )
  assume tgbtwndiff.a: |- ( ph -> A e. P )
  assume tgbtwndiff.b: |- ( ph -> B e. P )
  assume tgbtwndiff.l: |- ( ph -> 2 <_ ( # ` P ) )

  disjoint .- c
  disjoint A c
  disjoint B c
  disjoint I c
  disjoint P c
  disjoint c ph
  disjoint c u
  disjoint c v
  disjoint u v
  disjoint .- u
  disjoint .- v
  disjoint A u
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint I u
  disjoint I v
  disjoint P u
  disjoint P v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> E. c e. P ( B e. ( A I c ) /\ B =/= c ) )

  proof
    wph
    vu
    cv
    #
    vv
    cv
    #
    wne
    #
    cB
    cA
    vc
    cv
    #
    cI
    co
    wcel
    #
    cB
    @3
    wne
    #
    wa
    #
    vc
    cP
    wrex
    #
    vu
    vv
    cP
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @1
    cP
    wcel
    #
    wa
    #
    @2
    wa
    #
    @4
    cB
    @3
    c.mi
    co
    #
    @0
    @1
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vc
    cP
    wrex
    @7
    @12
    vc
    @0
    @1
    cP
    cG
    cI
    c.mi
    cA
    cB
    tgbtwndiff.p
    tgbtwndiff.d
    tgbtwndiff.i
    wph
    cG
    cstrkg
    wcel
    #
    @8
    @10
    @2
    tgbtwndiff.g
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    @8
    @10
    @2
    tgbtwndiff.a
    ad3antrrr
    wph
    cB
    cP
    wcel
    #
    @8
    @10
    @2
    tgbtwndiff.b
    ad3antrrr
    #
    wph
    @8
    @10
    @2
    simpllr
    #
    @9
    @10
    @2
    simplr
    #
    axtgsegcon
    @12
    @16
    @6
    vc
    cP
    @12
    @3
    cP
    wcel
    #
    wa
    #
    @15
    @5
    @4
    @24
    @15
    @5
    @24
    @15
    wa
    #
    cB
    @3
    @25
    cB
    @3
    wceq
    #
    @0
    @1
    wceq
    @25
    @26
    wa
    #
    cP
    cG
    cI
    c.mi
    @0
    @1
    cB
    tgbtwndiff.p
    tgbtwndiff.d
    tgbtwndiff.i
    @12
    @17
    @23
    @15
    @26
    @18
    ad3antrrr
    @12
    @8
    @23
    @15
    @26
    @21
    ad3antrrr
    @12
    @10
    @23
    @15
    @26
    @22
    ad3antrrr
    @12
    @19
    @23
    @15
    @26
    @20
    ad3antrrr
    @27
    cB
    cB
    c.mi
    co
    @13
    @14
    @27
    cB
    @3
    cB
    c.mi
    @25
    @26
    simpr
    oveq2d
    @24
    @15
    @26
    simplr
    eqtr2d
    axtgcgrid
    @27
    @0
    @1
    @11
    @2
    @23
    @15
    @26
    simp-4r
    neneqd
    pm2.65da
    neqned
    ex
    anim2d
    reximdva
    mpd
    wph
    vu
    vv
    cP
    cG
    cI
    c.mi
    tgbtwndiff.p
    tgbtwndiff.d
    tgbtwndiff.i
    tgbtwndiff.g
    tgbtwndiff.l
    tglowdim1
    r19.29vva
end
