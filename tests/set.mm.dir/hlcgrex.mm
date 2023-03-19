include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "axtgsegcon.mm"
include "wo.mm"
include "w3a.mm"
include "simprr.mm"
include "tgcgrcoml.mm"
include "eqcomd.mm"
include "ad4antr.mm"
include "tgcgrneq.mm"
include "simpllr.mm"
include "simprd.mm"
include "necomd.mm"
include "simprl.mm"
include "simpld.mm"
include "tgbtwncom.mm"
include "tgbtwnconn2.mm"
include "3jca.mm"
include "ishlg.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "nehash2.mm"
include "tgbtwndiff.mm"
include "r19.29a.mm"

theorem hlcgrex
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let c.mi: class .-
  let vy: setvar y
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )
  assume hltr.d: |- ( ph -> D e. P )
  assume hlcgrex.m: |- .- = ( dist ` G )
  assume hlcgrex.1: |- ( ph -> D =/= A )
  assume hlcgrex.2: |- ( ph -> B =/= C )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint K x
  disjoint I x
  disjoint P x
  disjoint ph x
  disjoint .- y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint K y
  disjoint I y
  disjoint P y
  disjoint ph y
  assert |- ( ph -> E. x e. P ( x ( K ` A ) D /\ ( A .- x ) = ( B .- C ) ) )

  proof
    wph
    cA
    cD
    vy
    cv
    #
    cI
    co
    wcel
    #
    cA
    @0
    wne
    #
    wa
    #
    vx
    cv
    #
    cD
    cA
    cK
    cfv
    wbr
    #
    cA
    @4
    c.mi
    co
    cB
    cC
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vx
    cP
    wrex
    #
    vy
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @3
    wa
    #
    cA
    @0
    @4
    cI
    co
    wcel
    #
    @7
    wa
    #
    vx
    cP
    wrex
    @9
    @12
    vx
    cB
    cC
    cP
    cG
    cI
    c.mi
    @0
    cA
    ishlg.p
    hlcgrex.m
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    #
    @10
    @3
    hlln.1
    ad2antrr
    #
    wph
    @10
    @3
    simplr
    #
    wph
    cA
    cP
    wcel
    #
    @10
    @3
    ishlg.a
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    #
    @10
    @3
    ishlg.b
    ad2antrr
    #
    wph
    cC
    cP
    wcel
    #
    @10
    @3
    ishlg.c
    ad2antrr
    #
    axtgsegcon
    @12
    @14
    @8
    vx
    cP
    @12
    @4
    cP
    wcel
    #
    wa
    #
    @14
    @8
    @25
    @14
    wa
    #
    @5
    @7
    @26
    @5
    @4
    cA
    wne
    #
    cD
    cA
    wne
    #
    @4
    cA
    cD
    cI
    co
    wcel
    cD
    cA
    @4
    cI
    co
    wcel
    wo
    #
    w3a
    @26
    @27
    @28
    @29
    @26
    cB
    cC
    @4
    cA
    cP
    cG
    cI
    c.mi
    ishlg.p
    hlcgrex.m
    ishlg.i
    @12
    @15
    @24
    @14
    @16
    ad2antrr
    #
    @12
    @20
    @24
    @14
    @21
    ad2antrr
    #
    @12
    @22
    @24
    @14
    @23
    ad2antrr
    #
    @12
    @24
    @14
    simplr
    #
    @12
    @18
    @24
    @14
    @19
    ad2antrr
    #
    @26
    @4
    cA
    c.mi
    co
    @6
    @26
    cA
    @4
    cB
    cC
    cP
    cG
    cI
    c.mi
    ishlg.p
    hlcgrex.m
    ishlg.i
    @30
    @34
    @33
    @31
    @32
    @25
    @13
    @7
    simprr
    #
    tgcgrcoml
    eqcomd
    wph
    cB
    cC
    wne
    @10
    @3
    @24
    @14
    hlcgrex.2
    ad4antr
    tgcgrneq
    wph
    @28
    @10
    @3
    @24
    @14
    hlcgrex.1
    ad4antr
    @26
    @0
    cA
    @4
    cD
    cP
    cG
    cI
    ishlg.p
    ishlg.i
    @30
    @12
    @10
    @24
    @14
    @17
    ad2antrr
    #
    @34
    @33
    wph
    cD
    cP
    wcel
    @10
    @3
    @24
    @14
    hltr.d
    ad4antr
    #
    @26
    cA
    @0
    @26
    @1
    @2
    @11
    @3
    @24
    @14
    simpllr
    #
    simprd
    necomd
    @25
    @13
    @7
    simprl
    @26
    cD
    cA
    @0
    cP
    cG
    cI
    c.mi
    ishlg.p
    hlcgrex.m
    ishlg.i
    @30
    @37
    @34
    @36
    @26
    @1
    @2
    @38
    simpld
    tgbtwncom
    tgbtwnconn2
    3jca
    @26
    @4
    cD
    cA
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    @33
    @37
    @34
    @30
    ishlg
    mpbird
    @35
    jca
    ex
    reximdva
    mpd
    wph
    cD
    cA
    cP
    cG
    cI
    c.mi
    vy
    ishlg.p
    hlcgrex.m
    ishlg.i
    hlln.1
    hltr.d
    ishlg.a
    wph
    cB
    cC
    cP
    cvv
    cP
    cvv
    wcel
    wph
    cP
    cG
    cbs
    cfv
    cvv
    ishlg.p
    cG
    cbs
    fvex
    eqeltri
    a1i
    ishlg.b
    ishlg.c
    hlcgrex.2
    nehash2
    tgbtwndiff
    r19.29a
end
